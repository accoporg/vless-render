/**
 * Production VLESS-over-WS Server for Render / Edge-TLS PaaS (render.js)
 * - Runs plain HTTP behind Render's TLS-terminating edge proxy (listens on process.env.PORT || 10000)
 * - Auto-registers RENDER_EXTERNAL_HOSTNAME (or PUBLIC_HOST) on port 443 with WORKER_BASE_URL on startup
 * - Supports VLESS TCP (0x01), UDP (0x02), and MuxCool/XUDP (0x03) with post-DNS SSRF protection
 * - Set LOG_VERBOSE=1 to log every TCP/UDP dial; defaults to [SYS] and [ERR] only
 */
(function bootstrap() {
const fs = require('fs');
const http = require('http');
const dns = require('dns');
const net = require('net');
const dgram = require('dgram');
const https = require('https');
const crypto = require('crypto');
const WebSocket = require('ws');

const os = require('os');
const { spawn } = require('child_process');

function detectContainerMemoryBytes() {
  const envMb = Number(process.env.MEMORY_LIMIT_MB || 0);
  if (Number.isFinite(envMb) && envMb >= 32) {
    return Math.round(envMb * 1024 * 1024);
  }
  const sysTotal = os.totalmem();
  let detected = sysTotal;

  // cgroups v2 (memory.max & memory.high)
  for (const cgPath of ['/sys/fs/cgroup/memory.max', '/sys/fs/cgroup/memory.high']) {
    try {
      const raw = fs.readFileSync(cgPath, 'utf8').trim();
      if (raw && raw !== 'max') {
        const val = Number(raw);
        if (Number.isFinite(val) && val >= 32 * 1024 * 1024 && val < detected) {
          detected = val;
        }
      }
    } catch {}
  }

  // cgroups v1 fallback (memory.limit_in_bytes)
  try {
    const raw = fs.readFileSync('/sys/fs/cgroup/memory/memory.limit_in_bytes', 'utf8').trim();
    if (raw) {
      const val = Number(raw);
      if (Number.isFinite(val) && val >= 32 * 1024 * 1024 && val < detected) {
        detected = val;
      }
    }
  } catch {}

  return detected;
}

const MEM_LIMIT_BYTES = detectContainerMemoryBytes();
const MEM_LIMIT_MB = Math.max(32, Math.round(MEM_LIMIT_BYTES / (1024 * 1024)));

// Auto-tune V8 old-space heap limit on constrained containers (<= 512 MB) before allocating runtime state
if (
  MEM_LIMIT_MB <= 512 &&
  process.env.VLESS_HEAP_TUNED !== '1' &&
  process.env.DISABLE_HEAP_TUNE !== '1'
) {
  const heapMb = Math.max(28, Math.min(240, Math.floor((MEM_LIMIT_MB - 36) * 0.62)));
  const child = spawn(
    process.execPath,
    [`--max-old-space-size=${heapMb}`, '--expose-gc', ...process.argv.slice(1)],
    {
      stdio: 'inherit',
      env: { ...process.env, VLESS_HEAP_TUNED: '1' }
    }
  );
  const forwardSig = (sig) => {
    try { child.kill(sig); } catch {}
  };
  process.on('SIGTERM', () => forwardSig('SIGTERM'));
  process.on('SIGINT', () => forwardSig('SIGINT'));
  child.on('exit', (code, signal) => {
    if (signal) process.exit(1);
    process.exit(code ?? 0);
  });
  // Pause parent execution while child runs
  setInterval(() => {}, 60000);
  return;
}

function buildResourceProfile(memMb) {
  if (memMb <= 128) {
    const maxTotal = Number(process.env.MAX_TOTAL_CONNS || Math.max(24, Math.floor((memMb - 44) * 0.85)));
    return {
      tier: 'nano',
      maxChunk: Number(process.env.MAX_WS_CHUNK || 8192),
      maxPayload: 256 * 1024,
      maxTotalConns: maxTotal,
      maxConnsPerToken: Number(process.env.MAX_CONNS_PER_TOKEN || Math.max(12, Math.floor(maxTotal / 3))),
      wsHighWater: 64 * 1024,
      wsLowWater: 16 * 1024,
      preconnectPause: 16 * 1024,
      preconnectMax: 64 * 1024,
      udpMaxBuffered: 64 * 1024,
      udpRxMax: 64 * 1024,
      muxMaxBuf: 128 * 1024,
      muxMaxSessions: 24,
      maxCacheEntries: 256,
      workerMaxSockets: 4
    };
  }
  if (memMb <= 256) {
    const maxTotal = Number(process.env.MAX_TOTAL_CONNS || Math.max(96, Math.floor((memMb - 48) * 0.88)));
    return {
      tier: 'micro',
      maxChunk: Number(process.env.MAX_WS_CHUNK || 16384),
      maxPayload: 512 * 1024,
      maxTotalConns: maxTotal,
      maxConnsPerToken: Number(process.env.MAX_CONNS_PER_TOKEN || Math.max(32, Math.floor(maxTotal / 3))),
      wsHighWater: 192 * 1024,
      wsLowWater: 48 * 1024,
      preconnectPause: 32 * 1024,
      preconnectMax: 131072,
      udpMaxBuffered: 131072,
      udpRxMax: 131072,
      muxMaxBuf: 262144,
      muxMaxSessions: 48,
      maxCacheEntries: 512,
      workerMaxSockets: 6
    };
  }
  const maxTotal = Number(process.env.MAX_TOTAL_CONNS || Math.min(512, Math.floor((memMb - 56) * 0.72)));
  return {
    tier: 'standard',
    maxChunk: Number(process.env.MAX_WS_CHUNK || 16384),
    maxPayload: 1024 * 1024,
    maxTotalConns: maxTotal,
    maxConnsPerToken: Number(process.env.MAX_CONNS_PER_TOKEN || Math.max(64, Math.floor(maxTotal / 3))),
    wsHighWater: 512 * 1024,
    wsLowWater: 128 * 1024,
    preconnectPause: 65536,
    preconnectMax: 262144,
    udpMaxBuffered: 262144,
    udpRxMax: 262144,
    muxMaxBuf: 524288,
    muxMaxSessions: 64,
    maxCacheEntries: 1024,
    workerMaxSockets: 8
  };
}

const RES = buildResourceProfile(MEM_LIMIT_MB);
const OOM_SOFT_BYTES = Math.floor(MEM_LIMIT_BYTES * 0.80);
const OOM_HARD_BYTES = Math.floor(MEM_LIMIT_BYTES * 0.88);
let memoryPressureActive = false;
let lastMemWarnAt = 0;

function trimBoundedMap(map, maxEntries) {
  if (map.size <= maxEntries) return;
  const excess = map.size - maxEntries;
  let removed = 0;
  for (const key of map.keys()) {
    map.delete(key);
    removed++;
    if (removed >= excess) break;
  }
}

function checkMemoryPressure() {
  const rss = process.memoryUsage().rss;
  if (rss >= OOM_SOFT_BYTES) {
    trimBoundedMap(dnsCache, Math.floor(RES.maxCacheEntries / 2));
    trimBoundedMap(tokenCache, Math.floor(RES.maxCacheEntries / 2));
    if (typeof global.gc === 'function') {
      try { global.gc(); } catch {}
    }
  }
  const afterRss = process.memoryUsage().rss;
  const wasActive = memoryPressureActive;
  memoryPressureActive = afterRss >= OOM_HARD_BYTES;
  if (memoryPressureActive && (!wasActive || Date.now() - lastMemWarnAt > 30000)) {
    lastMemWarnAt = Date.now();
    log('SYS', null, `Memory pressure guard active: RSS ${(afterRss / 1048576).toFixed(1)}/${MEM_LIMIT_MB}MB (pausing new upgrades)`);
  }
  return memoryPressureActive;
}

setInterval(checkMemoryPressure, 5000).unref();


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
const MAX_CHUNK = RES.maxChunk;
const LOG_VERBOSE = process.env.LOG_VERBOSE === '1';

let registered = false;

const VLESS_RESP_HEADER = Buffer.from([0x00, 0x00]);
const EMPTY_BUF = Buffer.alloc(0);
const MAX_CONNS_PER_TOKEN = RES.maxConnsPerToken;
const MAX_TOTAL_CONNS = RES.maxTotalConns;
const UPSTREAM_FAMILY = Number(process.env.UPSTREAM_FAMILY || 4);
const ALLOW_ALL_PORTS = process.env.ALLOW_ALL_PORTS === '1';

const BLOCKED_ABUSE_PORTS = new Set([21, 22, 23, 25, 69, 111, 135, 137, 138, 139, 179, 445, 554, 1433, 3306, 3389, 5900]);

const workerAgent = new https.Agent({
  keepAlive: true,
  maxSockets: RES.workerMaxSockets,
  keepAliveMsecs: 30000
});

let connSeq = 0;

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

/** @type {Map<string, number>} */
const activeTokenConns = new Map();

function incrementTokenConns(token) {
  if (!token) return;
  activeTokenConns.set(token, (activeTokenConns.get(token) || 0) + 1);
}

function decrementTokenConns(token) {
  if (!token) return;
  const cur = (activeTokenConns.get(token) || 0) - 1;
  if (cur <= 0) activeTokenConns.delete(token);
  else activeTokenConns.set(token, cur);
}

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
      trimBoundedMap(tokenDeltas, RES.maxCacheEntries);
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
  if (!ALLOW_ALL_PORTS && BLOCKED_ABUSE_PORTS.has(port)) return true;

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

/** @type {Map<string, { address: string, family: number, exp: number }>} */
const dnsCache = new Map();
const dnsInflight = new Map();

function resolveCachedDns(host) {
  const cleanHost = host.startsWith('[') && host.endsWith(']') ? host.slice(1, -1) : host;
  const ipVer = net.isIP(cleanHost);
  if (ipVer === 4 || ipVer === 6) {
    return Promise.resolve({ address: cleanHost, family: ipVer });
  }
  const now = Date.now();
  const cached = dnsCache.get(cleanHost);
  if (cached && cached.exp > now) {
    return Promise.resolve({ address: cached.address, family: cached.family });
  }
  const key = `${UPSTREAM_FAMILY}:${cleanHost}`;
  if (dnsInflight.has(key)) return dnsInflight.get(key);

  const p = new Promise((resolve, reject) => {
    const opts = UPSTREAM_FAMILY === 4 || UPSTREAM_FAMILY === 6
      ? { family: UPSTREAM_FAMILY, verbatim: false }
      : { verbatim: false };
    dns.lookup(cleanHost, opts, (err, address, family) => {
      if (err || !address) {
        if (UPSTREAM_FAMILY === 4) {
          return dns.lookup(cleanHost, { verbatim: false }, (err2, addr2, fam2) => {
            if (err2 || !addr2) return reject(err2 || err || new Error('ENOTFOUND'));
            dnsCache.set(cleanHost, { address: addr2, family: fam2, exp: Date.now() + 60000 });
            trimBoundedMap(dnsCache, RES.maxCacheEntries);
            resolve({ address: addr2, family: fam2 });
          });
        }
        return reject(err || new Error('ENOTFOUND'));
      }
      dnsCache.set(cleanHost, { address, family, exp: Date.now() + 60000 });
      trimBoundedMap(dnsCache, RES.maxCacheEntries);
      resolve({ address, family });
    });
  }).finally(() => {
    dnsInflight.delete(key);
  });

  dnsInflight.set(key, p);
  return p;
}

function sendSafeUdp(id, tag, sock4, getSock6, payload, port, host, onDone) {
  if (isBlockedTarget(host, port)) {
    nodeMetrics.errors.blocked++;
    if (onDone) onDone(new Error('BLOCKED_TARGET'));
    return;
  }
  resolveCachedDns(host)
    .then(({ address, family }) => {
      if (isBlockedTarget(address, port)) {
        nodeMetrics.errors.blocked++;
        log('ERR', id, `${tag} blocked resolved private IP -> ${host} (${address}:${port})`);
        if (onDone) onDone(new Error('BLOCKED_IP'));
        return;
      }
      const targetSock = family === 6 ? (typeof getSock6 === 'function' ? getSock6() : getSock6) : sock4;
      if (!targetSock) {
        if (onDone) onDone(new Error('NO_UDP_SOCKET'));
        return;
      }
      try {
        targetSock.send(payload, port, address, (err) => {
          if (err) {
            nodeMetrics.errors.upstream++;
            log('ERR', id, `${tag} send error -> ${host} (${address}:${port}): ${err.code || err.message}`);
          }
          if (onDone) onDone(err || null);
        });
      } catch (err) {
        nodeMetrics.errors.upstream++;
        if (onDone) onDone(err);
      }
    })
    .catch((err) => {
      nodeMetrics.errors.upstream++;
      log('ERR', id, `${tag} DNS error -> ${host}:${port} (${err.code || err.message})`);
      if (onDone) onDone(err);
    });
}

setInterval(() => {
  const now = Date.now();
  for (const [k, v] of dnsCache.entries()) {
    if (v.exp <= now) dnsCache.delete(k);
  }
}, 120000).unref();

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
          trimBoundedMap(tokenCache, RES.maxCacheEntries);
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
  maxPayload: RES.maxPayload,
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

function formatIpv6(buf, offset) {
  const parts = [];
  for (let i = 0; i < 16; i += 2) {
    parts.push(buf.readUInt16BE(offset + i).toString(16));
  }
  return parts.join(':');
}

function parseVlessAddress(buf, offset) {
  if (buf.length < offset + 1) return null;
  const addrType = buf[offset++];
  let host = '';
  if (addrType === 1) {
    if (buf.length < offset + 4) return null;
    host = `${buf[offset]}.${buf[offset + 1]}.${buf[offset + 2]}.${buf[offset + 3]}`;
    offset += 4;
  } else if (addrType === 2) {
    if (buf.length < offset + 1) return null;
    const len = buf[offset++];
    if (buf.length < offset + len) return null;
    host = buf.subarray(offset, offset + len).toString('utf8');
    offset += len;
  } else if (addrType === 3) {
    if (buf.length < offset + 16) return null;
    host = formatIpv6(buf, offset);
    offset += 16;
  } else {
    return { error: `addrType=${addrType}` };
  }
  return { host, nextOffset: offset };
}

function encodeMuxAddress(ip) {
  const ver = net.isIP(ip);
  if (ver === 4) {
    const p = ip.split('.').map(Number);
    return Buffer.from([0x01, p[0], p[1], p[2], p[3]]);
  }
  if (ver === 6) {
    const words = parseIpv6Words(ip);
    if (words) {
      const b = Buffer.allocUnsafe(17);
      b[0] = 0x03;
      for (let i = 0; i < 8; i++) b.writeUInt16BE(words[i], 1 + i * 2);
      return b;
    }
  }
  const strBuf = Buffer.from(String(ip || '0.0.0.0'), 'utf8');
  return Buffer.concat([Buffer.from([0x02, strBuf.length]), strBuf]);
}

function connectUpstreamTcp(id, tag, host, port, onConnect, onFail) {
  let destroyed = false;
  let socket = null;

  const connectTimer = setTimeout(() => {
    if (!destroyed) {
      destroyed = true;
      nodeMetrics.errors.timeout++;
      log('ERR', id, `${tag} connect timeout -> ${host}:${port}`);
      if (socket) socket.destroy();
      onFail(new Error('CONNECT_TIMEOUT'));
    }
  }, 3500);

  resolveCachedDns(host)
    .then(({ address, family }) => {
      if (destroyed) return;
      if (isBlockedTarget(address, port)) {
        destroyed = true;
        clearTimeout(connectTimer);
        nodeMetrics.errors.blocked++;
        log('ERR', id, `${tag} blocked resolved private IP -> ${host} (${address}:${port})`);
        return onFail(new Error('BLOCKED_IP'));
      }

      socket = net.connect({ host: address, port, family });
      socket.setNoDelay(true);
      socket.setKeepAlive(true, 15000);

      let connected = false;
      socket.once('connect', () => {
        if (destroyed) return socket.destroy();
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
        if (!connected && !destroyed) {
          destroyed = true;
          onFail(err);
        }
      });
    })
    .catch((err) => {
      if (destroyed) return;
      destroyed = true;
      clearTimeout(connectTimer);
      nodeMetrics.errors.upstream++;
      log('ERR', id, `${tag} upstream error -> ${host}:${port} (${err.code || err.message})`);
      onFail(err);
    });

  return {
    destroy() {
      destroyed = true;
      clearTimeout(connectTimer);
      if (socket && !socket.destroyed) socket.destroy();
    }
  };
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
    if (ws.bufferedAmount > RES.wsHighWater) {
      sock.pause();
      if (!drainTimer) {
        drainTimer = setInterval(() => {
          if (ws.readyState !== WebSocket.OPEN || ws.bufferedAmount < RES.wsLowWater) {
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
  let udp4 = null;
  let udp6 = null;
  let rxBuffer = EMPTY_BUF;
  let lastActivity = Date.now();
  let closed = false;

  log('VLESS-UDP', id, `Open -> ${targetHost}:${targetPort}`);

  const cleanup = () => {
    if (closed) return;
    closed = true;
    clearInterval(idleTimer);
    rxBuffer = EMPTY_BUF;
    if (udp4) {
      try { udp4.close(); } catch {}
      udp4 = null;
    }
    if (udp6) {
      try { udp6.close(); } catch {}
      udp6 = null;
    }
    if (ws.readyState === WebSocket.OPEN) ws.close();
  };

  const attachUdpListeners = (sock) => {
    sock.on('message', (msg) => {
      if (closed) return;
      lastActivity = Date.now();
      if (ws.readyState !== WebSocket.OPEN || ws.bufferedAmount > RES.udpMaxBuffered) {
        nodeMetrics.errors.udpDrop++;
        return;
      }
      recordTraffic(ws, 'rx', msg.length);
      const frame = Buffer.allocUnsafe(2 + msg.length);
      frame.writeUInt16BE(msg.length, 0);
      msg.copy(frame, 2);
      ws.send(frame, { binary: true });
    });
    sock.on('error', (err) => {
      if (!closed) {
        nodeMetrics.errors.upstream++;
        log('ERR', id, `VLESS-UDP socket error -> ${targetHost}:${targetPort}: ${err.code || err.message}`);
      }
      cleanup();
    });
  };

  const getUdp4 = () => {
    if (!udp4 && !closed) {
      udp4 = dgram.createSocket('udp4');
      attachUdpListeners(udp4);
    }
    return udp4;
  };

  const getUdp6 = () => {
    if (!udp6 && !closed) {
      udp6 = dgram.createSocket('udp6');
      attachUdpListeners(udp6);
    }
    return udp6;
  };

  if (targetHost.includes(':')) getUdp6();
  else getUdp4();

  const idleTimer = setInterval(() => {
    if (Date.now() - lastActivity > 60000) cleanup();
  }, 15000);
  idleTimer.unref();

  const flushFrames = (chunk) => {
    if (closed) return;
    lastActivity = Date.now();
    if (chunk && chunk.length > 0) {
      if (rxBuffer.length + chunk.length > RES.udpRxMax) {
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
        const packetCopy = Buffer.from(datagram);
        recordTraffic(ws, 'tx', packetCopy.length);
        sendSafeUdp(id, 'VLESS-UDP', getUdp4(), getUdp6, packetCopy, targetPort, targetHost);
      }
    }

    if (offset > 0) {
      rxBuffer = offset === rxBuffer.length ? EMPTY_BUF : rxBuffer.subarray(offset);
    }
  };

  ws.on('message', (data) => {
    flushFrames(Buffer.isBuffer(data) ? data : Buffer.from(data));
  });
  ws.on('error', cleanup);
  ws.on('close', cleanup);

  const respHeader = version === 0x00 ? VLESS_RESP_HEADER : Buffer.from([version, 0x00]);
  ws.send(respHeader, { binary: true }, (err) => {
    if (err) return cleanup();
    flushFrames(initialPayload);
  });
}

/**
 * VLESS MuxCool (cmd=0x03) demultiplexer for clients that enable Mux (e.g. v2rayN)
 */
function handleVlessMux(ws, id, version, initialPayload) {
  /** @type {Map<number, { type: 'tcp'|'udp', sock?: any, udp4?: dgram.Socket, udp6?: dgram.Socket, drainTimer?: any, host: string, port: number, hasAddrMeta?: boolean, globalId?: Buffer, lastActive: number, pending: Buffer[], pendingBytes: number, connected: boolean, closed: boolean }>} */
  const sessions = new Map();
  let muxBuf = EMPTY_BUF;
  let closed = false;

  log('VLESS-MUX', id, 'Opened MuxCool session');

  const sendMuxControl = (sessionId, status, opt = 0x00) => {
    if (closed || ws.readyState !== WebSocket.OPEN) return;
    const frame = Buffer.allocUnsafe(6);
    frame.writeUInt16BE(4, 0);
    frame.writeUInt16BE(sessionId, 2);
    frame[4] = status;
    frame[5] = opt;
    ws.send(frame, { binary: true });
  };

  const sendMuxTcpData = (sessionId, data) => {
    if (closed || ws.readyState !== WebSocket.OPEN || !data || data.length === 0) return;
    recordTraffic(ws, 'rx', data.length);
    for (let off = 0; off < data.length; off += MAX_CHUNK) {
      const slice = data.subarray(off, off + MAX_CHUNK);
      const frame = Buffer.allocUnsafe(8 + slice.length);
      frame.writeUInt16BE(4, 0);
      frame.writeUInt16BE(sessionId, 2);
      frame[4] = 0x02; // SessionStatusKeep
      frame[5] = 0x01; // OptionData
      frame.writeUInt16BE(slice.length, 6);
      slice.copy(frame, 8);
      ws.send(frame, { binary: true });
    }
  };

  const sendMuxUdpData = (sess, sessionId, msg, rinfo) => {
    if (closed || sess.closed || ws.readyState !== WebSocket.OPEN || !msg || msg.length === 0) return;
    recordTraffic(ws, 'rx', msg.length);
    if (sess.hasAddrMeta && rinfo && rinfo.address && rinfo.port) {
      const addrBytes = encodeMuxAddress(rinfo.address);
      const metaLen = 4 + 1 + 2 + addrBytes.length;
      const frame = Buffer.allocUnsafe(2 + metaLen + 2 + msg.length);
      frame.writeUInt16BE(metaLen, 0);
      frame.writeUInt16BE(sessionId, 2);
      frame[4] = 0x02; // SessionStatusKeep
      frame[5] = 0x01; // OptionData
      frame[6] = 0x02; // Network UDP
      frame.writeUInt16BE(rinfo.port, 7);
      addrBytes.copy(frame, 9);
      const dataLenOff = 2 + metaLen;
      frame.writeUInt16BE(msg.length, dataLenOff);
      msg.copy(frame, dataLenOff + 2);
      ws.send(frame, { binary: true });
    } else {
      const frame = Buffer.allocUnsafe(8 + msg.length);
      frame.writeUInt16BE(4, 0);
      frame.writeUInt16BE(sessionId, 2);
      frame[4] = 0x02;
      frame[5] = 0x01;
      frame.writeUInt16BE(msg.length, 6);
      msg.copy(frame, 8);
      ws.send(frame, { binary: true });
    }
  };

  const closeSession = (sessionId, notifyClient = true, isError = false) => {
    const s = sessions.get(sessionId);
    if (!s || s.closed) return;
    s.closed = true;
    sessions.delete(sessionId);
    if (s.drainTimer) {
      clearInterval(s.drainTimer);
      s.drainTimer = null;
    }
    s.pending.length = 0;
    s.pendingBytes = 0;
    if (s.sock) {
      try { s.sock.destroy(); } catch {}
      s.sock = null;
    }
    if (s.udp4) {
      try { s.udp4.close(); } catch {}
      s.udp4 = null;
    }
    if (s.udp6) {
      try { s.udp6.close(); } catch {}
      s.udp6 = null;
    }
    if (!closed && ws.readyState === WebSocket.OPEN) {
      let anyBlocked = false;
      for (const other of sessions.values()) {
        if (other.type === 'tcp' && other.connected && other.sock && other.sock.writableNeedDrain) {
          anyBlocked = true;
          break;
        }
      }
      if (!anyBlocked) resumeWsReceiver(ws);
    }
    if (notifyClient) sendMuxControl(sessionId, 0x03, isError ? 0x02 : 0x00);
  };

  const udpGcTimer = setInterval(() => {
    const now = Date.now();
    for (const [sid, s] of sessions.entries()) {
      if (s.type === 'udp' && now - s.lastActive > 60000) {
        closeSession(sid, true, false);
      }
    }
  }, 15000);
  udpGcTimer.unref();

  const cleanupAll = () => {
    if (closed) return;
    closed = true;
    clearInterval(udpGcTimer);
    muxBuf = EMPTY_BUF;
    for (const sid of Array.from(sessions.keys())) {
      closeSession(sid, false, false);
    }
    if (ws.readyState === WebSocket.OPEN) ws.close();
  };

  const openMuxTcpSession = (sessionId, host, port, firstData) => {
    if (sessions.has(sessionId)) {
      closeSession(sessionId, false, false);
    }
    if (sessions.size >= RES.muxMaxSessions || isBlockedTarget(host, port)) {
      if (isBlockedTarget(host, port)) nodeMetrics.errors.blocked++;
      return sendMuxControl(sessionId, 0x03, 0x02);
    }
    const firstBuf = firstData && firstData.length > 0 ? Buffer.from(firstData) : null;
    const sess = {
      type: 'tcp',
      host,
      port,
      lastActive: Date.now(),
      pending: firstBuf ? [firstBuf] : [],
      pendingBytes: firstBuf ? firstBuf.length : 0,
      connected: false,
      closed: false,
      drainTimer: null,
      sock: null
    };
    sessions.set(sessionId, sess);

    sess.sock = connectUpstreamTcp(
      id,
      `MUX#${sessionId}`,
      host,
      port,
      (sock) => {
        if (closed || sess.closed) return sock.destroy();
        sess.sock = sock;
        sess.connected = true;
        sess.lastActive = Date.now();
        for (const chunk of sess.pending) {
          recordTraffic(ws, 'tx', chunk.length);
          writeChunkedToTcp(sock, chunk);
        }
        sess.pending.length = 0;
        sess.pendingBytes = 0;

        sock.on('drain', () => {
          if (!closed && ws.readyState === WebSocket.OPEN) resumeWsReceiver(ws);
        });

        sock.on('data', (chunk) => {
          sess.lastActive = Date.now();
          sendMuxTcpData(sessionId, chunk);
          if (ws.bufferedAmount > RES.wsHighWater && !sock.destroyed) {
            sock.pause();
            if (!sess.drainTimer) {
              sess.drainTimer = setInterval(() => {
                if (closed || sess.closed || sock.destroyed || ws.bufferedAmount < RES.wsLowWater) {
                  clearInterval(sess.drainTimer);
                  sess.drainTimer = null;
                  if (!sock.destroyed && !closed && !sess.closed) sock.resume();
                }
              }, 20);
              sess.drainTimer.unref();
            }
          }
        });
        sock.on('end', () => closeSession(sessionId, true, false));
        sock.on('close', () => closeSession(sessionId, true, false));
      },
      () => closeSession(sessionId, true, true)
    );
  };

  const openMuxUdpSession = (sessionId, host, port, firstData, hasAddrMeta, globalId) => {
    if (sessions.has(sessionId)) {
      closeSession(sessionId, false, false);
    }
    if (sessions.size >= RES.muxMaxSessions || isBlockedTarget(host, port)) {
      if (isBlockedTarget(host, port)) nodeMetrics.errors.blocked++;
      return sendMuxControl(sessionId, 0x03, 0x02);
    }

    const sess = {
      type: 'udp',
      udp4: null,
      udp6: null,
      host,
      port,
      hasAddrMeta: Boolean(hasAddrMeta),
      globalId: globalId || null,
      lastActive: Date.now(),
      pending: [],
      pendingBytes: 0,
      connected: true,
      closed: false
    };

    const bindUdpListeners = (sock) => {
      sock.on('message', (msg, rinfo) => {
        if (closed || sess.closed) return;
        sess.lastActive = Date.now();
        if (ws.bufferedAmount > RES.udpMaxBuffered) {
          nodeMetrics.errors.udpDrop++;
          return;
        }
        sendMuxUdpData(sess, sessionId, msg, rinfo);
      });
      sock.on('error', () => closeSession(sessionId, true, true));
    };

    const getUdp4 = () => {
      if (!sess.udp4 && !closed && !sess.closed) {
        sess.udp4 = dgram.createSocket('udp4');
        bindUdpListeners(sess.udp4);
      }
      return sess.udp4;
    };

    const getUdp6 = () => {
      if (!sess.udp6 && !closed && !sess.closed) {
        sess.udp6 = dgram.createSocket('udp6');
        bindUdpListeners(sess.udp6);
      }
      return sess.udp6;
    };

    if (host.includes(':')) getUdp6();
    else getUdp4();

    sess.getUdp4 = getUdp4;
    sess.getUdp6 = getUdp6;
    sessions.set(sessionId, sess);

    if (firstData && firstData.length > 0) {
      const copy = Buffer.from(firstData);
      recordTraffic(ws, 'tx', copy.length);
      sendSafeUdp(id, `MUX-UDP#${sessionId}`, getUdp4(), getUdp6, copy, port, host);
    }
  };

  const consumeMux = (chunk) => {
    if (closed) return;
    if (chunk && chunk.length > 0) {
      if (muxBuf.length + chunk.length > RES.muxMaxBuf) {
        log('ERR', id, 'VLESS-MUX buffer overflow');
        return cleanupAll();
      }
      muxBuf = muxBuf.length === 0 ? chunk : Buffer.concat([muxBuf, chunk]);
    }

    let offset = 0;
    while (muxBuf.length - offset >= 2) {
      const metaLen = muxBuf.readUInt16BE(offset);
      if (metaLen < 4 || metaLen > 512) {
        log('ERR', id, `VLESS-MUX invalid metaLen=${metaLen}`);
        return cleanupAll();
      }
      if (muxBuf.length - offset < 2 + metaLen) break;

      const metaStart = offset + 2;
      const metaEnd = metaStart + metaLen;
      const sessionId = muxBuf.readUInt16BE(metaStart);
      const status = muxBuf[metaStart + 2];
      const option = muxBuf[metaStart + 3];
      const hasData = (option & 0x01) !== 0;

      let frameEnd = metaEnd;
      let payload = EMPTY_BUF;
      if (hasData) {
        if (muxBuf.length < frameEnd + 2) break;
        const dataLen = muxBuf.readUInt16BE(frameEnd);
        if (muxBuf.length < frameEnd + 2 + dataLen) break;
        payload = muxBuf.subarray(frameEnd + 2, frameEnd + 2 + dataLen);
        frameEnd += 2 + dataLen;
      }

      offset = frameEnd;

      if (status === 0x04) {
        // KeepAlive
        continue;
      }
      if (status === 0x01) {
        // New session: network(1) + port(2) + addrType(1) + addr [+ optional 8B XUDP GlobalID]
        if (metaLen < 8) {
          sendMuxControl(sessionId, 0x03, 0x02);
          continue;
        }
        const netType = muxBuf[metaStart + 4];
        const port = muxBuf.readUInt16BE(metaStart + 5);
        const parsedAddr = parseVlessAddress(muxBuf.subarray(0, metaEnd), metaStart + 7);
        if (!parsedAddr || parsedAddr.error) {
          sendMuxControl(sessionId, 0x03, 0x02);
          continue;
        }
        if (netType === 0x01) {
          openMuxTcpSession(sessionId, parsedAddr.host, port, payload);
        } else if (netType === 0x02) {
          const hasGlobalId = (metaEnd - parsedAddr.nextOffset) >= 8;
          const globalId = hasGlobalId ? Buffer.from(muxBuf.subarray(parsedAddr.nextOffset, parsedAddr.nextOffset + 8)) : null;
          openMuxUdpSession(sessionId, parsedAddr.host, port, payload, true, globalId);
        } else {
          sendMuxControl(sessionId, 0x03, 0x02);
        }
      } else if (status === 0x02) {
        // Keep (data frame or XUDP per-packet target override)
        const sess = sessions.get(sessionId);
        if (!sess || sess.closed) continue;
        sess.lastActive = Date.now();
        if (payload.length > 0) {
          if (sess.type === 'tcp') {
            if (sess.connected && sess.sock) {
              recordTraffic(ws, 'tx', payload.length);
              if (!writeChunkedToTcp(sess.sock, payload)) {
                pauseWsReceiver(ws);
              }
            } else if (sess.pending.length < 32 && sess.pendingBytes + payload.length <= RES.preconnectMax) {
              sess.pending.push(Buffer.from(payload));
              sess.pendingBytes += payload.length;
            } else {
              closeSession(sessionId, true, true);
            }
          } else if (sess.type === 'udp') {
            let destHost = sess.host;
            let destPort = sess.port;
            if (metaLen >= 8 && muxBuf[metaStart + 4] === 0x02) {
              sess.hasAddrMeta = true;
              const overridePort = muxBuf.readUInt16BE(metaStart + 5);
              const pAddr = parseVlessAddress(muxBuf.subarray(0, metaEnd), metaStart + 7);
              if (!pAddr || pAddr.error || isBlockedTarget(pAddr.host, overridePort)) {
                nodeMetrics.errors.blocked++;
                continue;
              }
              destHost = pAddr.host;
              destPort = overridePort;
            }
            const copy = Buffer.from(payload);
            recordTraffic(ws, 'tx', copy.length);
            sendSafeUdp(id, `MUX-UDP#${sessionId}`, sess.getUdp4(), sess.getUdp6, copy, destPort, destHost);
          }
        }
      } else if (status === 0x03) {
        closeSession(sessionId, false, false);
      }
    }

    if (offset > 0) {
      muxBuf = offset === muxBuf.length ? EMPTY_BUF : muxBuf.subarray(offset);
    }
  };

  ws.on('message', (data) => {
    consumeMux(Buffer.isBuffer(data) ? data : Buffer.from(data));
  });
  ws.on('error', cleanupAll);
  ws.on('close', cleanupAll);

  const respHeader = version === 0x00 ? VLESS_RESP_HEADER : Buffer.from([version, 0x00]);
  ws.send(respHeader, { binary: true }, (err) => {
    if (err) return cleanupAll();
    consumeMux(initialPayload);
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
    if (buf.length < 19 || buf[0] !== 0x00) {
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
    if (buf.length < offset + 1) return ws.close();

    const cmd = buf[offset++];

    // VLESS Mux (cmd=0x03) omits port & address in the outer header
    if (cmd === 0x03) {
      return handleVlessMux(ws, id, version, buf.subarray(offset));
    }

    if (buf.length < offset + 4) return ws.close();
    const targetPort = buf.readUInt16BE(offset);
    offset += 2;

    const parsedAddr = parseVlessAddress(buf, offset);
    if (!parsedAddr) return ws.close();
    if (parsedAddr.error) {
      log('ERR', id, `VLESS unsupported ${parsedAddr.error}`);
      return ws.close();
    }

    const targetHost = parsedAddr.host;
    offset = parsedAddr.nextOffset;

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
      if (pendingBytes + b.length > RES.preconnectMax) {
        pendingChunks.length = 0;
        if (remoteSocket) remoteSocket.destroy();
        if (ws.readyState === WebSocket.OPEN) ws.close(1009, 'Pre-connect buffer exceeded');
        return;
      }
      pendingChunks.push(b);
      pendingBytes += b.length;
      if (pendingChunks.length > 16 || pendingBytes >= RES.preconnectPause) {
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
    memLimitBytes: MEM_LIMIT_BYTES,
    memProfile: RES.tier,
    maxTotalConns: RES.maxTotalConns,
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

setInterval(sendHeartbeat, 60000).unref();

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
    memLimitBytes: MEM_LIMIT_BYTES,
    memProfile: RES.tier,
    maxTotalConns: RES.maxTotalConns,
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

  if (memoryPressureActive || checkMemoryPressure() || wss.clients.size >= MAX_TOTAL_CONNS) {
    if (socket.writable) socket.write('HTTP/1.1 503 Service Unavailable\r\nConnection: close\r\n\r\n');
    return socket.destroy();
  }

  const { pathname, token: queryToken } = parseUpgradeUrl(request.url);
  const token = request.headers['x-relay-token'] || queryToken;
  const clientIp = extractClientIp(request);

  if (!(await verifyTokenWithWorker(token))) {
    nodeMetrics.errors.auth++;
    log('AUTH', id, `Rejected upgrade ${pathname} from ${clientIp}`);
    if (socket.writable) socket.write('HTTP/1.1 401 Unauthorized\r\nConnection: close\r\n\r\n');
    return socket.destroy();
  }

  if (socket.destroyed || !socket.writable) {
    return socket.destroy();
  }

  if (memoryPressureActive || checkMemoryPressure() || wss.clients.size >= MAX_TOTAL_CONNS) {
    socket.write('HTTP/1.1 503 Service Unavailable\r\nConnection: close\r\n\r\n');
    return socket.destroy();
  }

  if ((activeTokenConns.get(token) || 0) >= MAX_CONNS_PER_TOKEN) {
    socket.write('HTTP/1.1 429 Too Many Requests\r\nConnection: close\r\n\r\n');
    return socket.destroy();
  }

  if (pathname === '/vless') {
    incrementTokenConns(token);
    let decDone = false;
    const safeDec = () => {
      if (decDone) return;
      decDone = true;
      decrementTokenConns(token);
    };
    socket.once('close', safeDec);

    wss.handleUpgrade(request, socket, head, (ws) => {
      ws.meta = { ip: clientIp, token, connectedAt: Date.now(), tx: 0, rx: 0 };
      ws.once('close', safeDec);
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
  log('SYS', null, `VLESS Render/Edge-TLS (/vless, ram=${MEM_LIMIT_MB}MB[${RES.tier}], maxConns=${RES.maxTotalConns}, chunk=${MAX_CHUNK}B) listening on 0.0.0.0:${PORT}`);
  registerRenderHost();
});

})();
