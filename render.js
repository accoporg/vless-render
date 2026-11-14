/**
 * Production VLESS-over-WS Server for Render / Edge-TLS PaaS (render.js)
 * - Runs plain HTTP behind Render's TLS-terminating edge proxy (listens on process.env.PORT || 10000)
 * - Auto-registers RENDER_EXTERNAL_HOSTNAME (or PUBLIC_HOST) on port 443 with WORKER_BASE_URL on startup
 * - Reports live heartbeats, RAM/uptime, per-token bandwidth, and active client IPs to Worker
 * - Set LOG_VERBOSE=1 to log every TCP/UDP dial; defaults to [SYS] and [ERR] only
 */
const http = require('http');
const net = require('net');
const dgram = require('dgram');
const https = require('https');
const crypto = require('crypto');
const WebSocket = require('ws');

const PORT = Number(process.env.PORT || process.env.SERVER_PORT || 10000);
const WORKER_BASE_URL = (process.env.WORKER_BASE_URL || 'https://connect.accopture.top').replace(/\/$/, '');
const ADMIN_BOOTSTRAP_TOKEN = process.env.ADMIN_BOOTSTRAP_TOKEN || 'f665ac0c4af3b4d6c676e7b86fecf70e2ce7e94b42206a0a4afbc49636ea4850';
const PUBLIC_HOST = (process.env.PUBLIC_HOST || process.env.RENDER_EXTERNAL_HOSTNAME || '')
  .replace(/^https?:\/\//i, '')
  .replace(/\/.*$/, '')
  .trim();
const PUBLIC_PORT = Number(process.env.PUBLIC_PORT || 443);
const VLESS_UUID = (process.env.VLESS_UUID || 'b831381d-6324-4d53-ad4f-8cda48b30811')
  .replace(/-/g, '')
  .toLowerCase();
const VLESS_UUID_BYTES = Buffer.from(VLESS_UUID, 'hex');
const MAX_CHUNK = Number(process.env.MAX_WS_CHUNK || 16384);
const LOG_VERBOSE = process.env.LOG_VERBOSE === '1';

const VLESS_RESP_HEADER = Buffer.from([0x00, 0x00]);
const EMPTY_BUF = Buffer.alloc(0);

const workerAgent = new https.Agent({
  keepAlive: true,
  maxSockets: 8,
  keepAliveMsecs: 30000
});

let connSeq = 0;
let registered = false;

const nodeMetrics = {
  startedAt: Date.now(),
  totalConns: 0,
  txDelta: 0,
  rxDelta: 0,
  errors: {
    timeout: 0,
    upstream: 0,
    udpDrop: 0,
    auth: 0,
    blocked: 0
  }
};

/** @type {Map<string, { tx: number, rx: number, conns: number, lastSeen: number }>} */
const tokenDeltas = new Map();

function recordTraffic(ws, dir, bytes) {
  if (!bytes || bytes <= 0) return;
  const now = Date.now();
  if (dir === 'tx') {
    nodeMetrics.txDelta += bytes;
    if (ws && ws.meta) ws.meta.tx += bytes;
  } else {
    nodeMetrics.rxDelta += bytes;
    if (ws && ws.meta) ws.meta.rx += bytes;
  }
  const tok = ws && ws.meta && ws.meta.token;
  if (tok) {
    let entry = tokenDeltas.get(tok);
    if (!entry) {
      entry = { tx: 0, rx: 0, conns: 0, lastSeen: now };
      tokenDeltas.set(tok, entry);
    }
    if (dir === 'tx') entry.tx += bytes;
    else entry.rx += bytes;
    entry.lastSeen = now;
  }
}

function recordConnOpen(token) {
  nodeMetrics.totalConns++;
  if (!token) return;
  const now = Date.now();
  let entry = tokenDeltas.get(token);
  if (!entry) {
    entry = { tx: 0, rx: 0, conns: 0, lastSeen: now };
    tokenDeltas.set(token, entry);
  }
  entry.conns++;
  entry.lastSeen = now;
}

function log(tag, id, msg) {
  if (!LOG_VERBOSE && tag !== 'ERR' && tag !== 'SYS') return;
  const ts = new Date().toISOString().slice(11, 23);
  console.log(`[${ts}] [${tag}]${id ? ` [#${id}]` : ''} ${msg}`);
}

function isBlockedIpv4Octets(a, b, c, d) {
  return (
    a === 0 ||
    a === 10 ||
    a === 127 ||
    (a === 100 && b >= 64 && b <= 127) ||
    (a === 169 && b === 254) ||
    (a === 172 && b >= 16 && b <= 31) ||
    (a === 192 && b === 0 && c === 0) ||
    (a === 192 && b === 0 && c === 2) ||
    (a === 192 && b === 168) ||
    (a === 198 && (b === 18 || b === 19)) ||
    (a === 198 && b === 51 && c === 100) ||
    (a === 203 && b === 0 && c === 113) ||
    a >= 224
  );
}

function parseIpv6Words(addr) {
  let s = addr.toLowerCase();
  const zoneIdx = s.indexOf('%');
  if (zoneIdx !== -1) s = s.slice(0, zoneIdx);

  if (s.includes('.')) {
    const lastColon = s.lastIndexOf(':');
    if (lastColon === -1) return null;
    const v4Part = s.slice(lastColon + 1);
    const octets = v4Part.split('.').map(Number);
    if (octets.length !== 4 || octets.some(n => !Number.isInteger(n) || n < 0 || n > 255)) return null;
    const wHigh = ((octets[0] << 8) | octets[1]).toString(16);
    const wLow = ((octets[2] << 8) | octets[3]).toString(16);
    s = `${s.slice(0, lastColon)}:${wHigh}:${wLow}`;
  }

  const dbl = s.split('::');
  if (dbl.length > 2) return null;
  const left = dbl[0] ? dbl[0].split(':') : [];
  const right = dbl.length === 2 && dbl[1] ? dbl[1].split(':') : [];
  const missing = 8 - (left.length + right.length);
  if ((dbl.length === 1 && missing !== 0) || (dbl.length === 2 && missing < 1)) return null;

  const full = [...left, ...new Array(Math.max(0, missing)).fill('0'), ...right];
  if (full.length !== 8) return null;
  const words = new Uint16Array(8);
  for (let i = 0; i < 8; i++) {
    const v = parseInt(full[i], 16);
    if (Number.isNaN(v) || v < 0 || v > 0xffff) return null;
    words[i] = v;
  }
  return words;
}

function isBlockedTarget(host, port) {
  if (!host || port <= 0 || port > 65535) return true;
  const cleanHost = host.startsWith('[') && host.endsWith(']') ? host.slice(1, -1) : host;
  const lower = cleanHost.toLowerCase();
  if (
    lower === 'localhost' ||
    lower.endsWith('.localhost') ||
    lower.endsWith('.local') ||
    lower.endsWith('.internal') ||
    lower.endsWith('.lan')
  ) {
    return true;
  }

  const ipVer = net.isIP(cleanHost);
  if (ipVer === 4) {
    const parts = cleanHost.split('.').map(Number);
    return isBlockedIpv4Octets(parts[0], parts[1], parts[2], parts[3]);
  }
  if (ipVer === 6) {
    const w = parseIpv6Words(cleanHost);
    if (!w) return true;
    const isAllZeroTop80 = w[0] === 0 && w[1] === 0 && w[2] === 0 && w[3] === 0 && w[4] === 0;
    if (isAllZeroTop80 && w[5] === 0 && w[6] === 0 && (w[7] === 0 || w[7] === 1)) {
      return true;
    }
    if (isAllZeroTop80 && (w[5] === 0xffff || w[5] === 0)) {
      const a = (w[6] >> 8) & 0xff;
      const b = w[6] & 0xff;
      const c = (w[7] >> 8) & 0xff;
      const d = w[7] & 0xff;
      if (isBlockedIpv4Octets(a, b, c, d)) return true;
    }
    if (w[0] === 0x0064 && w[1] === 0xff9b && w[2] === 0 && w[3] === 0 && w[4] === 0 && w[5] === 0) {
      const a = (w[6] >> 8) & 0xff;
      const b = w[6] & 0xff;
      const c = (w[7] >> 8) & 0xff;
      const d = w[7] & 0xff;
      if (isBlockedIpv4Octets(a, b, c, d)) return true;
    }
    if ((w[0] & 0xfe00) === 0xfc00) return true;
    if ((w[0] & 0xffc0) === 0xfe80) return true;
    if ((w[0] & 0xff00) === 0xff00) return true;
    if (w[0] === 0x2001 && w[1] === 0x0db8) return true;
  }
  return false;
}

function registerRenderHost() {
  if (!PUBLIC_HOST) return;
  const payload = JSON.stringify({
    host: PUBLIC_HOST,
    port: PUBLIC_PORT,
    replaceHost: true
  });
  const req = https.request(
    `${WORKER_BASE_URL}/api/register`,
    {
      method: 'POST',
      agent: workerAgent,
      headers: {
        'Content-Type': 'application/json',
        'Content-Length': Buffer.byteLength(payload),
        'x-auth-token': ADMIN_BOOTSTRAP_TOKEN
      },
      timeout: 8000
    },
    (res) => {
      res.resume();
      if (res.statusCode === 200) {
        registered = true;
        log('SYS', null, `Registered ${PUBLIC_HOST}:${PUBLIC_PORT} with Worker`);
        setTimeout(sendHeartbeat, 1000).unref();
      } else {
        log('ERR', null, `Worker registration returned HTTP ${res.statusCode}`);
      }
    }
  );
  req.on('error', (err) => log('ERR', null, `Worker registration error: ${err.message}`));
  req.on('timeout', () => { req.destroy(); });
  req.write(payload);
  req.end();
}

const tokenCache = new Map();
const pendingChecks = new Map();

function queryWorkerVerify(token) {
  if (pendingChecks.has(token)) return pendingChecks.get(token);

  const p = new Promise((resolve) => {
    const req = https.get(
      `${WORKER_BASE_URL}/api/verify?token=${encodeURIComponent(token)}`,
      { agent: workerAgent, timeout: 5000 },
      (res) => {
        res.resume();
        const now = Date.now();
        if (res.statusCode === 200) {
          tokenCache.set(token, {
            freshUntil: now + 5 * 60 * 1000,
            staleUntil: now + 15 * 60 * 1000
          });
          resolve(true);
        } else {
          tokenCache.delete(token);
          log('AUTH', null, `Worker rejected token (HTTP ${res.statusCode})`);
          resolve(false);
        }
      }
    );
    req.on('error', (err) => {
      log('ERR', null, `Worker verify network error: ${err.code || err.message}`);
      resolve(false);
    });
    req.on('timeout', () => {
      log('ERR', null, 'Worker verify request timed out');
      req.destroy();
      resolve(false);
    });
  }).finally(() => {
    pendingChecks.delete(token);
  });

  pendingChecks.set(token, p);
  return p;
}

async function verifyTokenWithWorker(token) {
  if (!token || typeof token !== 'string' || token.length > 256) return false;
  const now = Date.now();
  const entry = tokenCache.get(token);

  if (entry) {
    if (entry.freshUntil > now) return true;
    if (entry.staleUntil > now) {
      queryWorkerVerify(token).catch(() => {});
      return true;
    }
  }
  return queryWorkerVerify(token);
}

setInterval(() => {
  const now = Date.now();
  for (const [tok, entry] of tokenCache.entries()) {
    if (entry.staleUntil <= now) tokenCache.delete(tok);
  }
}, 300000).unref();

const wss = new WebSocket.Server({
  noServer: true,
  maxPayload: 2 * 1024 * 1024,
  perMessageDeflate: false
});

setInterval(() => {
  for (const ws of wss.clients) {
    if (ws.readyState === WebSocket.OPEN && ws.bufferedAmount === 0) {
      try { ws.ping(); } catch {}
    }
  }
}, 25000).unref();

function collectActiveClients() {
  const grouped = new Map();
  for (const ws of wss.clients) {
    if (ws.readyState !== WebSocket.OPEN || !ws.meta) continue;
    const key = `${ws.meta.ip}|${ws.meta.token}`;
    let item = grouped.get(key);
    if (!item) {
      item = {
        ip: ws.meta.ip,
        token: ws.meta.token,
        conns: 0,
        tx: 0,
        rx: 0,
        connectedAt: ws.meta.connectedAt
      };
      grouped.set(key, item);
    }
    item.conns++;
    item.tx += ws.meta.tx;
    item.rx += ws.meta.rx;
    if (ws.meta.connectedAt < item.connectedAt) {
      item.connectedAt = ws.meta.connectedAt;
    }
  }
  return Array.from(grouped.values())
    .sort((a, b) => (b.tx + b.rx) - (a.tx + a.rx))
    .slice(0, 50);
}

let heartbeatInFlight = false;
function sendHeartbeat() {
  if (!PUBLIC_HOST || heartbeatInFlight) return;
  if (!registered) registerRenderHost();
  heartbeatInFlight = true;

  const mem = process.memoryUsage();
  const txSnap = nodeMetrics.txDelta;
  const rxSnap = nodeMetrics.rxDelta;
  const tokSnap = {};
  for (const [tok, val] of tokenDeltas.entries()) {
    tokSnap[tok] = { ...val };
  }

  const payload = JSON.stringify({
    host: PUBLIC_HOST,
    port: PUBLIC_PORT,
    runtime: 'render',
    uptimeSec: Math.floor(process.uptime()),
    rssBytes: mem.rss,
    heapUsedBytes: mem.heapUsed,
    activeWs: wss.clients.size,
    totalConns: nodeMetrics.totalConns,
    txDelta: txSnap,
    rxDelta: rxSnap,
    errors: { ...nodeMetrics.errors },
    clients: collectActiveClients(),
    tokenDeltas: tokSnap
  });

  const req = https.request(
    `${WORKER_BASE_URL}/api/heartbeat`,
    {
      method: 'POST',
      agent: workerAgent,
      headers: {
        'Content-Type': 'application/json',
        'Content-Length': Buffer.byteLength(payload),
        'x-auth-token': ADMIN_BOOTSTRAP_TOKEN
      },
      timeout: 6000
    },
    (res) => {
      res.resume();
      heartbeatInFlight = false;
      if (res.statusCode === 200) {
        nodeMetrics.txDelta = Math.max(0, nodeMetrics.txDelta - txSnap);
        nodeMetrics.rxDelta = Math.max(0, nodeMetrics.rxDelta - rxSnap);
        for (const [tok, sent] of Object.entries(tokSnap)) {
          const cur = tokenDeltas.get(tok);
          if (!cur) continue;
          cur.tx = Math.max(0, cur.tx - sent.tx);
          cur.rx = Math.max(0, cur.rx - sent.rx);
          cur.conns = Math.max(0, cur.conns - sent.conns);
          if (cur.tx === 0 && cur.rx === 0 && cur.conns === 0) {
            tokenDeltas.delete(tok);
          }
        }
      }
    }
  );
  req.on('error', () => { heartbeatInFlight = false; });
  req.on('timeout', () => { heartbeatInFlight = false; req.destroy(); });
  req.write(payload);
  req.end();
}

setInterval(sendHeartbeat, 30000).unref();

function formatIpv6(buf, offset) {
  const parts = [];
  for (let i = 0; i < 16; i += 2) {
    parts.push(buf.readUInt16BE(offset + i).toString(16));
  }
  return parts.join(':');
}

function connectUpstreamTcp(id, tag, host, port, onConnect, onFail) {
  const isIpv6Literal = host.includes(':');
  const isIpv4Literal = /^\d{1,3}(\.\d{1,3}){3}$/.test(host);
  const options = {
    host,
    port,
    family: isIpv6Literal ? 6 : (isIpv4Literal ? 4 : 0),
    autoSelectFamily: !isIpv6Literal && !isIpv4Literal,
    autoSelectFamilyAttemptTimeout: 250
  };

  const socket = net.connect(options);
  socket.setNoDelay(true);
  socket.setKeepAlive(true, 15000);

  let connected = false;
  const connectTimer = setTimeout(() => {
    if (!connected) {
      nodeMetrics.errors.timeout++;
      log('ERR', id, `${tag} connect timeout -> ${host}:${port}`);
      socket.destroy();
      onFail(new Error('CONNECT_TIMEOUT'));
    }
  }, 5000);

  socket.once('connect', () => {
    connected = true;
    clearTimeout(connectTimer);
    socket.setTimeout(300000);
    socket.on('timeout', () => socket.destroy());
    onConnect(socket);
  });

  socket.on('error', (err) => {
    clearTimeout(connectTimer);
    if (err.code !== 'ECONNRESET' && err.code !== 'EPIPE') {
      nodeMetrics.errors.upstream++;
      log('ERR', id, `${tag} upstream error -> ${host}:${port} (${err.code || err.message})`);
    }
    socket.destroy();
    if (!connected) onFail(err);
  });

  return socket;
}

function writeChunkedToTcp(sock, buf) {
  if (!buf || buf.length === 0 || sock.destroyed || !sock.writable) return true;
  if (buf.length <= MAX_CHUNK) return sock.write(buf);
  let ok = true;
  for (let offset = 0; offset < buf.length; offset += MAX_CHUNK) {
    if (!sock.write(buf.subarray(offset, offset + MAX_CHUNK))) ok = false;
  }
  return ok;
}

function pauseWsReceiver(ws) {
  const rawSock = ws._socket;
  if (rawSock && !rawSock.destroyed) rawSock.pause();
}

function resumeWsReceiver(ws) {
  const rawSock = ws._socket;
  if (rawSock && !rawSock.destroyed) rawSock.resume();
}

function pumpBidirectional(ws, sock, earlyPayload, pendingChunks, onTxBytes, onRxBytes, onFinish) {
  let inflightWsSends = 0;
  let upstreamEnded = false;
  let closeCode = null;
  let drainTimer = null;
  let finished = false;

  const tryCloseWs = () => {
    if (upstreamEnded && inflightWsSends === 0 && ws.readyState === WebSocket.OPEN) {
      if (closeCode !== null) {
        ws.close(closeCode);
      } else {
        ws.close();
      }
    }
  };

  const checkWsBackpressure = () => {
    if (ws.readyState !== WebSocket.OPEN) return;
    if (ws.bufferedAmount > 512 * 1024) {
      sock.pause();
      if (!drainTimer) {
        drainTimer = setInterval(() => {
          if (ws.readyState !== WebSocket.OPEN || ws.bufferedAmount < 128 * 1024) {
            clearInterval(drainTimer);
            drainTimer = null;
            if (!sock.destroyed) sock.resume();
          }
        }, 15);
      }
    }
  };

  let tcpSaturated = false;
  if (earlyPayload && earlyPayload.length > 0) {
    recordTraffic(ws, 'tx', earlyPayload.length);
    if (!writeChunkedToTcp(sock, earlyPayload)) tcpSaturated = true;
  }

  if (pendingChunks && pendingChunks.length > 0) {
    for (let i = 0; i < pendingChunks.length; i++) {
      const c = pendingChunks[i];
      recordTraffic(ws, 'tx', c.length);
      if (onTxBytes) onTxBytes(c.length);
      if (!writeChunkedToTcp(sock, c)) tcpSaturated = true;
    }
    pendingChunks.length = 0;
  }

  if (tcpSaturated) pauseWsReceiver(ws);

  ws.on('message', (data) => {
    const chunk = Buffer.isBuffer(data) ? data : Buffer.from(data);
    recordTraffic(ws, 'tx', chunk.length);
    if (onTxBytes) onTxBytes(chunk.length);
    if (!writeChunkedToTcp(sock, chunk)) {
      pauseWsReceiver(ws);
    }
  });

  sock.on('drain', () => {
    if (ws.readyState === WebSocket.OPEN) resumeWsReceiver(ws);
  });

  sock.on('data', (chunk) => {
    recordTraffic(ws, 'rx', chunk.length);
    if (onRxBytes) onRxBytes(chunk.length);
    if (ws.readyState !== WebSocket.OPEN) return;

    if (chunk.length <= MAX_CHUNK) {
      inflightWsSends++;
      ws.send(chunk, { binary: true }, () => {
        inflightWsSends--;
        tryCloseWs();
      });
    } else {
      for (let offset = 0; offset < chunk.length; offset += MAX_CHUNK) {
        const slice = chunk.subarray(offset, offset + MAX_CHUNK);
        inflightWsSends++;
        ws.send(slice, { binary: true }, () => {
          inflightWsSends--;
          tryCloseWs();
        });
      }
    }
    checkWsBackpressure();
  });

  const cleanup = (who) => {
    if (finished) return;
    finished = true;
    if (drainTimer) {
      clearInterval(drainTimer);
      drainTimer = null;
    }
    if (onFinish) onFinish(who);
  };

  sock.on('end', () => {
    cleanup('remote-eof');
    upstreamEnded = true;
    closeCode = 1000;
    tryCloseWs();
  });

  sock.on('close', () => {
    cleanup('remote-close');
    upstreamEnded = true;
    tryCloseWs();
  });

  ws.on('close', (code) => {
    cleanup(`ws-close:${code}`);
    if (!sock.destroyed) sock.destroy();
  });

  if (!tcpSaturated) resumeWsReceiver(ws);
}

function handleVlessUdp(ws, id, version, targetHost, targetPort, initialPayload) {
  const isIpv6 = targetHost.includes(':');
  const udpSocket = dgram.createSocket(isIpv6 ? 'udp6' : 'udp4');
  let rxBuffer = EMPTY_BUF;
  let lastActivity = Date.now();
  let closed = false;

  log('VLESS-UDP', id, `Open -> ${targetHost}:${targetPort}`);

  const cleanup = () => {
    if (closed) return;
    closed = true;
    clearInterval(idleTimer);
    rxBuffer = EMPTY_BUF;
    try { udpSocket.close(); } catch {}
    if (ws.readyState === WebSocket.OPEN) ws.close();
  };

  const idleTimer = setInterval(() => {
    if (Date.now() - lastActivity > 60000) cleanup();
  }, 15000);
  idleTimer.unref();

  const flushFrames = (chunk) => {
    if (closed) return;
    lastActivity = Date.now();
    if (chunk && chunk.length > 0) {
      if (rxBuffer.length + chunk.length > 262144) {
        log('ERR', id, 'VLESS-UDP rxBuffer overflow');
        return cleanup();
      }
      rxBuffer = rxBuffer.length === 0 ? chunk : Buffer.concat([rxBuffer, chunk]);
    }

    let offset = 0;
    while (rxBuffer.length - offset >= 2) {
      const pktLen = rxBuffer.readUInt16BE(offset);
      if (rxBuffer.length - offset < 2 + pktLen) break;
      const datagram = rxBuffer.subarray(offset + 2, offset + 2 + pktLen);
      offset += 2 + pktLen;
      if (datagram.length > 0 && !closed) {
        recordTraffic(ws, 'tx', datagram.length);
        udpSocket.send(datagram, targetPort, targetHost, (err) => {
          if (err && !closed) {
            nodeMetrics.errors.upstream++;
            log('ERR', id, `VLESS-UDP send error -> ${targetHost}:${targetPort}: ${err.code || err.message}`);
          }
        });
      }
    }

    if (offset > 0) {
      rxBuffer = offset === rxBuffer.length ? EMPTY_BUF : rxBuffer.subarray(offset);
    }
  };

  ws.on('message', (data) => {
    flushFrames(Buffer.isBuffer(data) ? data : Buffer.from(data));
  });

  udpSocket.on('message', (msg) => {
    if (closed) return;
    lastActivity = Date.now();
    if (ws.readyState !== WebSocket.OPEN || ws.bufferedAmount > 262144) {
      nodeMetrics.errors.udpDrop++;
      return;
    }
    recordTraffic(ws, 'rx', msg.length);
    const frame = Buffer.allocUnsafe(2 + msg.length);
    frame.writeUInt16BE(msg.length, 0);
    msg.copy(frame, 2);
    ws.send(frame, { binary: true });
  });

  udpSocket.on('error', (err) => {
    if (!closed) {
      nodeMetrics.errors.upstream++;
      log('ERR', id, `VLESS-UDP socket error -> ${targetHost}:${targetPort}: ${err.code || err.message}`);
    }
    cleanup();
  });
  ws.on('error', cleanup);
  ws.on('close', cleanup);

  const respHeader = version === 0x00 ? VLESS_RESP_HEADER : Buffer.from([version, 0x00]);
  ws.send(respHeader, { binary: true }, (err) => {
    if (err) return cleanup();
    flushFrames(initialPayload);
  });
}

function handleVlessConnection(ws, id) {
  let remoteSocket = null;
  const handshakeTimer = setTimeout(() => {
    if (!remoteSocket && ws.readyState === WebSocket.OPEN) ws.close(1008, 'Handshake timeout');
  }, 8000);

  ws.once('message', (msg) => {
    clearTimeout(handshakeTimer);
    const buf = Buffer.isBuffer(msg) ? msg : Buffer.from(msg);
    if (buf.length < 24 || buf[0] !== 0x00) {
      log('ERR', id, `VLESS invalid header (len=${buf.length}, ver=${buf[0]})`);
      return ws.close();
    }

    const version = buf[0];
    const clientUuid = buf.subarray(1, 17);
    if (!crypto.timingSafeEqual(clientUuid, VLESS_UUID_BYTES)) {
      log('ERR', id, 'VLESS UUID mismatch');
      return ws.close();
    }

    let offset = 18 + buf[17];
    if (buf.length < offset + 4) return ws.close();

    const cmd = buf[offset++];
    const targetPort = buf.readUInt16BE(offset);
    offset += 2;
    const addrType = buf[offset++];
    let targetHost = '';

    if (addrType === 1) {
      if (buf.length < offset + 4) return ws.close();
      targetHost = `${buf[offset]}.${buf[offset + 1]}.${buf[offset + 2]}.${buf[offset + 3]}`;
      offset += 4;
    } else if (addrType === 2) {
      if (buf.length < offset + 1) return ws.close();
      const len = buf[offset++];
      if (buf.length < offset + len) return ws.close();
      targetHost = buf.subarray(offset, offset + len).toString('utf8');
      offset += len;
    } else if (addrType === 3) {
      if (buf.length < offset + 16) return ws.close();
      targetHost = formatIpv6(buf, offset);
      offset += 16;
    } else {
      log('ERR', id, `VLESS unsupported addrType=${addrType}`);
      return ws.close();
    }

    if (isBlockedTarget(targetHost, targetPort)) {
      nodeMetrics.errors.blocked++;
      log('ERR', id, `Blocked private/loopback target -> ${targetHost}:${targetPort}`);
      return ws.close(1008, 'Forbidden target');
    }

    const earlyPayload = buf.subarray(offset);

    if (cmd === 0x02) {
      return handleVlessUdp(ws, id, version, targetHost, targetPort, earlyPayload);
    }
    if (cmd !== 0x01) {
      log('ERR', id, `VLESS unsupported cmd=0x${cmd.toString(16)} -> ${targetHost}:${targetPort}`);
      return ws.close();
    }

    log('VLESS-TCP', id, `Dialing ${targetHost}:${targetPort} (early=${earlyPayload.length}B)`);

    let txBytes = earlyPayload.length;
    let rxBytes = 0;
    let closedLogged = false;
    const logClose = (who) => {
      if (closedLogged) return;
      closedLogged = true;
      log('VLESS-TCP', id, `Closed ${targetHost}:${targetPort} by=${who} tx=${txBytes}B rx=${rxBytes}B`);
    };

    const pendingChunks = [];
    let pendingBytes = 0;
    const onEarlyMessage = (chunk) => {
      const b = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
      if (pendingBytes + b.length > 262144) {
        pendingChunks.length = 0;
        if (remoteSocket) remoteSocket.destroy();
        if (ws.readyState === WebSocket.OPEN) ws.close(1009, 'Pre-connect buffer exceeded');
        return;
      }
      pendingChunks.push(b);
      pendingBytes += b.length;
      if (pendingChunks.length > 16 || pendingBytes >= 65536) {
        pauseWsReceiver(ws);
      }
    };
    ws.on('message', onEarlyMessage);

    remoteSocket = connectUpstreamTcp(
      id,
      'VLESS-TCP',
      targetHost,
      targetPort,
      (sock) => {
        ws.removeListener('message', onEarlyMessage);
        if (ws.readyState !== WebSocket.OPEN) return sock.destroy();

        const respHeader = version === 0x00 ? VLESS_RESP_HEADER : Buffer.from([version, 0x00]);
        ws.send(respHeader, { binary: true }, (err) => {
          if (err) return sock.destroy();
          log('VLESS-TCP', id, `Connected ${targetHost}:${targetPort}`);
          pumpBidirectional(
            ws,
            sock,
            earlyPayload,
            pendingChunks,
            LOG_VERBOSE ? (n) => { txBytes += n; } : null,
            LOG_VERBOSE ? (n) => { rxBytes += n; } : null,
            LOG_VERBOSE ? (who) => logClose(who) : null
          );
        });
      },
      () => {
        ws.removeListener('message', onEarlyMessage);
        pendingChunks.length = 0;
        if (ws.readyState === WebSocket.OPEN) ws.close();
      }
    );
  });

  ws.on('error', () => {
    clearTimeout(handshakeTimer);
    if (remoteSocket) remoteSocket.destroy();
  });
  ws.on('close', () => {
    clearTimeout(handshakeTimer);
    if (remoteSocket) remoteSocket.destroy();
  });
}

function parseUpgradeUrl(rawUrl) {
  if (!rawUrl || typeof rawUrl !== 'string') return { pathname: '', token: '' };
  const qIdx = rawUrl.indexOf('?');
  if (qIdx === -1) return { pathname: rawUrl, token: '' };
  const pathname = rawUrl.slice(0, qIdx);
  const query = rawUrl.slice(qIdx + 1);
  let token = '';
  const pairs = query.split('&');
  for (let i = 0; i < pairs.length; i++) {
    const p = pairs[i];
    if (p.startsWith('token=')) {
      try {
        token = decodeURIComponent(p.slice(6));
      } catch {
        token = p.slice(6);
      }
      break;
    }
  }
  return { pathname, token };
}

function extractClientIp(request) {
  const direct = request.headers['true-client-ip'] || request.headers['cf-connecting-ip'];
  if (typeof direct === 'string' && direct.trim()) {
    return direct.trim().replace(/^::ffff:/, '');
  }
  const xff = request.headers['x-forwarded-for'];
  if (typeof xff === 'string' && xff.trim()) {
    const first = xff.split(',')[0].trim().replace(/^::ffff:/, '');
    if (first) return first;
  }
  return (request.socket.remoteAddress || '').replace(/^::ffff:/, '') || 'unknown';
}

let cachedHealthBody = '';
let cachedHealthExp = 0;
function getHealthJson() {
  const now = Date.now();
  if (now < cachedHealthExp && cachedHealthBody) return cachedHealthBody;
  const mem = process.memoryUsage();
  cachedHealthBody = JSON.stringify({
    ok: true,
    runtime: 'render',
    uptimeSec: Math.floor(process.uptime()),
    rssBytes: mem.rss,
    activeWs: wss.clients.size,
    totalConns: nodeMetrics.totalConns
  });
  cachedHealthExp = now + 1000;
  return cachedHealthBody;
}

process.on('uncaughtException', (err) => log('ERR', null, `Uncaught exception: ${err.message}`));
process.on('unhandledRejection', (reason) => log('ERR', null, `Unhandled rejection: ${reason}`));
process.on('SIGTERM', () => { sendHeartbeat(); setTimeout(() => process.exit(0), 250); });
process.on('SIGINT', () => { sendHeartbeat(); setTimeout(() => process.exit(0), 250); });

const httpServer = http.createServer((req, res) => {
  if (req.url === '/health') {
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(getHealthJson());
    return;
  }
  res.writeHead(200, { 'Content-Type': 'text/plain' });
  res.end('OK\n');
});

httpServer.on('connection', (socket) => {
  socket.setNoDelay(true);
  socket.setKeepAlive(true, 15000);
});

httpServer.on('upgrade', async (request, socket, head) => {
  const id = ++connSeq;
  socket.on('error', () => socket.destroy());
  socket.setNoDelay(true);

  const { pathname, token: queryToken } = parseUpgradeUrl(request.url);
  const token = request.headers['x-relay-token'] || queryToken;
  const clientIp = extractClientIp(request);

  if (!(await verifyTokenWithWorker(token))) {
    nodeMetrics.errors.auth++;
    log('AUTH', id, `Rejected upgrade ${pathname} from ${clientIp}`);
    if (socket.writable) socket.write('HTTP/1.1 401 Unauthorized\r\nConnection: close\r\n\r\n');
    return socket.destroy();
  }

  if (pathname === '/vless') {
    wss.handleUpgrade(request, socket, head, (ws) => {
      ws.meta = { ip: clientIp, token, connectedAt: Date.now(), tx: 0, rx: 0 };
      recordConnOpen(token);
      handleVlessConnection(ws, id);
    });
  } else {
    log('ERR', id, `404 upgrade path: ${pathname}`);
    if (socket.writable) socket.write('HTTP/1.1 404 Not Found\r\nConnection: close\r\n\r\n');
    socket.destroy();
  }
});

httpServer.listen(PORT, '0.0.0.0', () => {
  log('SYS', null, `VLESS Render/Edge-TLS (/vless, chunk=${MAX_CHUNK}B) listening on 0.0.0.0:${PORT}`);
  registerRenderHost();
});
