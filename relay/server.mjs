import crypto from 'node:crypto';
import fs from 'node:fs';
import http from 'node:http';
import https from 'node:https';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { promisify } from 'node:util';
import { gzip } from 'node:zlib';

const gzipAsync = promisify(gzip);

const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const MAX_WS_PAYLOAD_BYTES = 4 * 1024 * 1024;
const MAX_ASSET_BODY_BYTES = 4 * 1024 * 1024;
const MAX_WS_DROP_LOW_PRIORITY_BYTES = 64 * 1024;
const CLIENT_IDLE_TIMEOUT_MS = 65 * 1000;
const ASSET_WAIT_MAX_WAITERS = 64;
const ALLOWED_ASSET_PATH =
  /^(?:audio(?:-opus)?\/[a-z0-9_-]+\.(?:webm|mp3|opus|ogg|m4a|wav)|portraits\/[a-z0-9_-]+\.(?:webp|png|jpg)|sfx\/[a-z0-9_-]+\.(?:mp3|webm|ogg|wav))$/i;
const AUDIO_ASSET_PATH = /^audio(?:-opus)?\//i;
const COMPRESSIBLE_EXTS = new Set(['.html', '.js', '.mjs', '.css', '.json', '.svg', '.webmanifest']);

const MIME_TYPES = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'application/javascript; charset=utf-8',
  '.mjs': 'application/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.webmanifest': 'application/manifest+json; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.jpeg': 'image/jpeg',
  '.webp': 'image/webp',
  '.ico': 'image/x-icon',
  '.woff2': 'font/woff2',
  '.woff': 'font/woff',
  '.webm': 'audio/webm',
  '.mp3': 'audio/mpeg',
  '.opus': 'audio/ogg',
  '.ogg': 'audio/ogg',
  '.m4a': 'audio/mp4',
  '.wav': 'audio/wav',
};

const CORS_HEADERS = {
  'Access-Control-Allow-Origin': '*',
  'Access-Control-Allow-Methods': 'GET, HEAD, POST, OPTIONS',
  'Access-Control-Allow-Headers': 'Content-Type, X-Host-Token, X-Asset-Status, X-Asset-Req-Id, Range',
  'Access-Control-Max-Age': '86400',
  'X-Content-Type-Options': 'nosniff',
};

function sanitizeRoomCode(raw) {
  return String(raw || '').replace(/[^0-9A-Za-z]/g, '').toUpperCase().slice(0, 16);
}

function encodeWsFrame(payloadBuf, opcode = 0x1) {
  const len = payloadBuf.length;
  let header;
  if (len < 126) {
    header = Buffer.allocUnsafe(2);
    header[0] = 0x80 | opcode;
    header[1] = len;
  } else if (len < 65536) {
    header = Buffer.allocUnsafe(4);
    header[0] = 0x80 | opcode;
    header[1] = 126;
    header.writeUInt16BE(len, 2);
  } else {
    header = Buffer.allocUnsafe(10);
    header[0] = 0x80 | opcode;
    header[1] = 127;
    header.writeBigUInt64BE(BigInt(len), 2);
  }
  return Buffer.concat([header, payloadBuf]);
}

function sendWsText(socket, text) {
  if (!socket || socket.destroyed || !socket.writable) return;
  try {
    socket.write(encodeWsFrame(Buffer.from(text, 'utf8'), 0x1));
  } catch {
    // ignore broken pipe
  }
}

function sendWsPong(socket, payload) {
  if (!socket || socket.destroyed || !socket.writable) return;
  try {
    socket.write(encodeWsFrame(payload || Buffer.alloc(0), 0xA));
  } catch {
    // ignore
  }
}

function sendWsPing(socket) {
  if (!socket || socket.destroyed || !socket.writable) return;
  try {
    socket.write(encodeWsFrame(Buffer.alloc(0), 0x9));
  } catch {
    // ignore
  }
}

function sendWsClose(socket) {
  if (!socket || socket.destroyed || !socket.writable) return;
  try {
    socket.write(encodeWsFrame(Buffer.alloc(0), 0x8));
  } catch {
    // ignore
  }
}

function attachWsFrameParser(socket, handlers) {
  let buffer = Buffer.alloc(0);
  let fragChunks = [];
  let fragOpcode = 0;

  socket.on('data', (chunk) => {
    buffer = buffer.length === 0 ? chunk : Buffer.concat([buffer, chunk]);

    while (buffer.length >= 2) {
      const b0 = buffer[0];
      const b1 = buffer[1];
      const fin = (b0 & 0x80) !== 0;
      const opcode = b0 & 0x0f;
      const masked = (b1 & 0x80) !== 0;
      let payloadLen = b1 & 0x7f;
      let offset = 2;

      if (payloadLen === 126) {
        if (buffer.length < 4) return;
        payloadLen = buffer.readUInt16BE(2);
        offset = 4;
      } else if (payloadLen === 127) {
        if (buffer.length < 10) return;
        const bigLen = buffer.readBigUInt64BE(2);
        if (bigLen > BigInt(MAX_WS_PAYLOAD_BYTES)) {
          socket.destroy();
          return;
        }
        payloadLen = Number(bigLen);
        offset = 10;
      }

      if (payloadLen > MAX_WS_PAYLOAD_BYTES) {
        socket.destroy();
        return;
      }

      const maskLen = masked ? 4 : 0;
      const frameEnd = offset + maskLen + payloadLen;
      if (buffer.length < frameEnd) return;

      const payload = Buffer.from(buffer.subarray(offset + maskLen, frameEnd));
      if (masked) {
        const maskKey = buffer.subarray(offset, offset + 4);
        for (let i = 0; i < payload.length; i += 1) {
          payload[i] ^= maskKey[i & 3];
        }
      }
      buffer = buffer.subarray(frameEnd);

      if (opcode === 0x8) {
        sendWsClose(socket);
        socket.end();
        return;
      }
      handlers.onActivity?.();
      if (opcode === 0x9) {
        sendWsPong(socket, payload);
        continue;
      }
      if (opcode === 0xA) {
        continue;
      }

      if (opcode === 0x1 || opcode === 0x2) {
        if (fin) {
          if (opcode === 0x1) handlers.onText(payload.toString('utf8'));
        } else {
          fragOpcode = opcode;
          fragChunks = [payload];
        }
      } else if (opcode === 0x0) {
        fragChunks.push(payload);
        if (fin) {
          const full = Buffer.concat(fragChunks);
          const op = fragOpcode;
          fragChunks = [];
          fragOpcode = 0;
          if (op === 0x1) handlers.onText(full.toString('utf8'));
        }
      }
    }
  });
}

function createBufferLruCache(maxBytes) {
  const entries = new Map();
  let bytes = 0;

  return {
    get(key) {
      const hit = entries.get(key);
      if (!hit) return undefined;
      entries.delete(key);
      entries.set(key, hit);
      return hit;
    },
    set(key, value) {
      const size = value.data.length;
      if (size > maxBytes) return;
      const existing = entries.get(key);
      if (existing) {
        bytes -= existing.data.length;
        entries.delete(key);
      }
      while (entries.size > 0 && bytes + size > maxBytes) {
        const oldestKey = entries.keys().next().value;
        bytes -= entries.get(oldestKey).data.length;
        entries.delete(oldestKey);
      }
      entries.set(key, value);
      bytes += size;
    },
    clear() {
      entries.clear();
      bytes = 0;
    },
  };
}

function parseByteRange(header, total) {
  if (!header) return undefined;
  const match = /^bytes=(\d*)-(\d*)$/.exec(header);
  if (!match || (!match[1] && !match[2]) || total === 0) return null;
  const first = Number(match[1]);
  const second = Number(match[2]);
  const start = match[1] ? first : Math.max(0, total - second);
  const end = match[1] && match[2] ? Math.min(total - 1, second) : total - 1;
  return start <= end && start < total ? { start, end } : null;
}

function serveBufferedAsset(res, method, rangeHeader, data, contentType, cacheControl) {
  if (res.destroyed) return;
  const total = data.length;
  const headers = {
    ...CORS_HEADERS,
    'Content-Type': contentType,
    'Cache-Control': cacheControl,
    'Accept-Ranges': 'bytes',
  };
  const range = parseByteRange(rangeHeader, total);
  if (range === null) {
    res.writeHead(416, { ...headers, 'Content-Range': 'bytes */' + total }).end();
    return;
  }
  const head = method === 'HEAD';
  headers['Content-Length'] = range ? range.end - range.start + 1 : total;
  if (range) headers['Content-Range'] = `bytes ${range.start}-${range.end}/${total}`;
  res.writeHead(range ? 206 : 200, headers);
  if (head || total === 0) res.end();
  else res.end(range ? data.subarray(range.start, range.end + 1) : data);
}

function writeJson(res, statusCode, data, head = false) {
  if (res.destroyed || res.headersSent) return;
  const body = Buffer.from(JSON.stringify(data), 'utf8');
  res.writeHead(statusCode, {
    ...CORS_HEADERS,
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': 'no-store',
    'Content-Length': body.length,
  });
  res.end(head ? undefined : body);
}

async function readRequestBody(req, maxBytes) {
  const chunks = [];
  let total = 0;
  for await (const chunk of req) {
    const buf = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
    total += buf.length;
    if (total > maxBytes) {
      const err = new Error('Payload too large');
      err.statusCode = 413;
      throw err;
    }
    chunks.push(buf);
  }
  return Buffer.concat(chunks);
}

/**
 * Provider-agnostic HTTPS/WSS WebSocket & ephemeral asset proxy relay server.
 * Zero authoritative game state lives on this server: rooms exist only while
 * their host connects and recover seamlessly after a relay restart once the host
 * reconnects with the same roomCode + hostToken.
 */
export function createRelayServer({
  port = 8787,
  host = '0.0.0.0',
  webGuestDir = null,
  tls = null,
  maxRooms = 32,
  maxClientsPerRoom = 48,
  maxRoomCacheBytes = 8 * 1024 * 1024,
  maxBackpressureBytes = 1024 * 1024,
  assetTimeoutMs = 15000,
  roomGraceMs = 60000,
} = {}) {
  const resolvedGuestDir = webGuestDir ? path.resolve(webGuestDir) : null;
  const hasGuestDir = Boolean(resolvedGuestDir && fs.existsSync(resolvedGuestDir));
  const staticGzipCache = createBufferLruCache(4 * 1024 * 1024);

  const rooms = new Map();
  let guestSeq = 0;
  let keepaliveTimer = null;

  function failPendingAsset(room, reqId, statusCode, message) {
    const pending = room.pendingAssets.get(reqId);
    if (!pending) return;
    room.pendingAssets.delete(reqId);
    if (room.inFlightByPath.get(pending.path) === reqId) {
      room.inFlightByPath.delete(pending.path);
    }
    clearTimeout(pending.timer);
    for (const waiter of pending.waiters) {
      if (!waiter.res.destroyed && !waiter.res.headersSent) {
        waiter.res.writeHead(statusCode, { ...CORS_HEADERS, 'Cache-Control': 'no-store' }).end(message || '');
      }
    }
  }

  function destroyRoom(roomCode) {
    const room = rooms.get(roomCode);
    if (!room) return;
    if (room.graceTimer) {
      clearTimeout(room.graceTimer);
      room.graceTimer = null;
    }
    for (const reqId of [...room.pendingAssets.keys()]) {
      failPendingAsset(room, reqId, 503, 'Host offline');
    }
    if (room.hostSocket && !room.hostSocket.destroyed) {
      sendWsClose(room.hostSocket);
      room.hostSocket.destroy();
    }
    for (const sock of room.guests.values()) {
      if (!sock.destroyed) {
        sendWsClose(sock);
        sock.destroy();
      }
    }
    room.guests.clear();
    room.authenticatedPeers.clear();
    room.clientLastSeen.clear();
    room.assetCache.clear();
    rooms.delete(roomCode);
  }

  function dropGuest(room, peerId, reason) {
    room.authenticatedPeers.delete(peerId);
    room.clientLastSeen.delete(peerId);
    const sock = room.guests.get(peerId);
    if (!sock) return;
    room.guests.delete(peerId);
    if (!sock.destroyed) {
      try {
        sock.destroy();
      } catch {
        // ignore
      }
    }
    if (room.hostSocket && !room.hostSocket.destroyed) {
      sendWsText(room.hostSocket, JSON.stringify({ __relay: 'client_disconnected', peerId, reason }));
    }
  }

  function writeClientFrame(room, peerId, clientSock, frame, isLowPriority) {
    if (!clientSock || clientSock.destroyed || !clientSock.writable) return;
    if (clientSock.writableLength > maxBackpressureBytes) {
      dropGuest(room, peerId, 'backpressure');
      return;
    }
    if (isLowPriority && clientSock.writableLength > MAX_WS_DROP_LOW_PRIORITY_BYTES) {
      return;
    }
    try {
      clientSock.write(frame);
    } catch {
      // ignore broken pipe
    }
  }

  async function serveStaticGuest(req, res, reqPath) {
    let targetPath = reqPath === '/' ? '/index.html' : reqPath;
    if (/[\\:\x00-\x1f]/.test(targetPath) || targetPath.split('/').some((part) => /[ .]$/.test(part))) {
      res.writeHead(403, CORS_HEADERS).end();
      return;
    }
    let filePath = path.resolve(resolvedGuestDir, targetPath.replace(/^\/+/u, ''));
    if (!filePath.startsWith(resolvedGuestDir + path.sep)) {
      res.writeHead(403, CORS_HEADERS).end();
      return;
    }
    const statOrMissing = (file) =>
      fs.promises.stat(file).catch((err) => {
        if (err.code === 'ENOENT' || err.code === 'ENOTDIR') return undefined;
        throw err;
      });
    let stat = await statOrMissing(filePath);
    if (!stat?.isFile() && !path.extname(targetPath)) {
      filePath = path.join(resolvedGuestDir, 'index.html');
      stat = await statOrMissing(filePath);
    }
    if (!stat?.isFile()) {
      res.writeHead(404, CORS_HEADERS).end();
      return;
    }

    const ext = path.extname(filePath).toLowerCase();
    const head = req.method === 'HEAD';
    const mime = MIME_TYPES[ext] || 'application/octet-stream';
    const headers = {
      ...CORS_HEADERS,
      'Content-Type': mime,
      'Cache-Control': ext === '.html' ? 'no-cache' : 'public, max-age=86400, immutable',
    };
    const encodings = new Map(String(req.headers['accept-encoding'] ?? '').split(',').map((part) => {
      const [encoding, ...params] = part.trim().toLowerCase().split(';');
      const quality = params.find((param) => /^q\s*=/.test(param.trim()));
      return [encoding.trim(), quality ? Number(quality.split('=')[1]) : 1];
    }));
    const gzipAccepted = (encodings.get('gzip') ?? encodings.get('*') ?? 0) > 0;
    const compressible = COMPRESSIBLE_EXTS.has(ext);
    if (compressible) headers.Vary = 'Accept-Encoding';
    const alternatives = [['br', '.br'], ['gzip', '.gz']]
      .map(([encoding, suffix]) => ({ encoding, suffix, quality: encodings.get(encoding) ?? encodings.get('*') ?? 0 }))
      .filter(({ quality }) => quality > 0)
      .sort((a, b) => b.quality - a.quality);
    for (const { encoding, suffix } of compressible ? alternatives : []) {
      const sidecar = filePath + suffix;
      const packed = await statOrMissing(sidecar);
      if (!packed?.isFile()) continue;
      res.writeHead(200, { ...headers, 'Content-Encoding': encoding, 'Content-Length': packed.size });
      res.end(head ? undefined : await fs.promises.readFile(sidecar));
      return;
    }

    if (compressible && gzipAccepted && stat.size <= 4 * 1024 * 1024) {
      const cacheKey = `${filePath}:${stat.size}:${stat.mtimeMs}`;
      let cached = staticGzipCache.get(cacheKey);
      if (!cached) {
        const gz = await gzipAsync(await fs.promises.readFile(filePath), { level: 6 });
        cached = { data: gz, contentType: mime };
        staticGzipCache.set(cacheKey, cached);
      }
      res.writeHead(200, {
        ...headers,
        'Content-Encoding': 'gzip',
        Vary: 'Accept-Encoding',
        'Content-Length': cached.data.length,
      });
      res.end(head ? undefined : cached.data);
      return;
    }

    const raw = await fs.promises.readFile(filePath);
    res.writeHead(200, { ...headers, 'Content-Length': raw.length });
    res.end(head ? undefined : raw);
  }

  async function handleHttp(req, res) {
    if (req.method === 'OPTIONS') {
      res.writeHead(204, CORS_HEADERS).end();
      return;
    }

    const requestUrl = new URL(req.url || '/', 'http://localhost');
    let reqPath;
    try {
      reqPath = '/' + decodeURIComponent(requestUrl.pathname).split('/').filter(Boolean).join('/');
    } catch {
      res.writeHead(400, CORS_HEADERS).end();
      return;
    }

    const isHead = req.method === 'HEAD';
    if ((req.method === 'GET' || isHead) && reqPath === '/healthz') {
      writeJson(res, 200, { ok: true, service: 'touhou-karuta-relay', rooms: rooms.size }, isHead);
      return;
    }

    const relayPingMatch = /^\/relay\/rooms\/([^/]+)\/api\/lan-ping$/i.exec(reqPath);
    if ((req.method === 'GET' || isHead) && (relayPingMatch || reqPath === '/api/lan-ping')) {
      const rawCode = relayPingMatch ? relayPingMatch[1] : requestUrl.searchParams.get('room');
      const roomCode = sanitizeRoomCode(rawCode);
      const room = rooms.get(roomCode);
      if (!room) {
        writeJson(res, 404, { ok: false, error: 'Room not found' }, isHead);
        return;
      }
      writeJson(res, 200, {
        ok: true,
        app: 'touhou-karuta',
        roomCode: room.roomCode,
        passwordRequired: room.passwordRequired,
        hostOnline: Boolean(room.hostSocket && !room.hostSocket.destroyed),
        relay: true,
      }, isHead);
      return;
    }

    const assetPostWithIdMatch = /^\/relay\/rooms\/([^/]+)\/asset-response\/([a-f0-9]{16,48})$/i.exec(reqPath);
    const assetPostHeaderMatch = /^\/relay\/rooms\/([^/]+)\/asset-response$/i.exec(reqPath);
    if (req.method === 'POST' && (assetPostWithIdMatch || assetPostHeaderMatch)) {
      const roomCode = sanitizeRoomCode((assetPostWithIdMatch || assetPostHeaderMatch)[1]);
      const headerReqId = String(req.headers['x-asset-req-id'] || '').trim();
      const reqId = assetPostWithIdMatch
        ? assetPostWithIdMatch[2]
        : /^[a-f0-9]{16,48}$/i.test(headerReqId) ? headerReqId : '';
      if (!reqId) {
        writeJson(res, 400, { ok: false, error: 'Missing request id' });
        return;
      }
      const room = rooms.get(roomCode);
      if (!room) {
        writeJson(res, 404, { ok: false, error: 'Room not found' });
        return;
      }
      if (String(req.headers['x-host-token'] || '') !== room.hostToken) {
        writeJson(res, 403, { ok: false, error: 'Forbidden' });
        return;
      }
      let body;
      try {
        body = await readRequestBody(req, MAX_ASSET_BODY_BYTES);
      } catch (err) {
        writeJson(res, err.statusCode || 400, { ok: false, error: err.message });
        return;
      }

      const pending = room.pendingAssets.get(reqId);
      if (!pending) {
        writeJson(res, 200, { ok: true, expired: true });
        return;
      }
      room.pendingAssets.delete(reqId);
      if (room.inFlightByPath.get(pending.path) === reqId) {
        room.inFlightByPath.delete(pending.path);
      }
      clearTimeout(pending.timer);

      const upstreamStatus = Number.parseInt(String(req.headers['x-asset-status'] || '200'), 10);
      const ext = path.extname(pending.path).toLowerCase();
      const contentType = String(req.headers['content-type'] || MIME_TYPES[ext] || 'application/octet-stream');

      if (Number.isFinite(upstreamStatus) && upstreamStatus >= 200 && upstreamStatus < 300) {
        const isAudio = AUDIO_ASSET_PATH.test(pending.path);
        room.assetCache.set(pending.path, { data: body, contentType });
        const cacheControl = isAudio && room.passwordRequired ? 'private, no-store'
          : pending.path.startsWith('portraits/') ? 'public, max-age=86400, immutable'
          : 'public, max-age=3600';
        for (const waiter of pending.waiters) {
          serveBufferedAsset(waiter.res, waiter.method, waiter.rangeHeader, body, contentType, cacheControl);
        }
      } else {
        const errStatus = Number.isFinite(upstreamStatus) && upstreamStatus >= 400 ? upstreamStatus : 502;
        for (const waiter of pending.waiters) {
          if (!waiter.res.destroyed && !waiter.res.headersSent) {
            waiter.res.writeHead(errStatus, { ...CORS_HEADERS, 'Cache-Control': 'no-store' }).end();
          }
        }
      }
      writeJson(res, 200, { ok: true });
      return;
    }

    const assetGetMatch = /^\/relay\/rooms\/([^/]+)\/(.+)$/i.exec(reqPath);
    if ((req.method === 'GET' || req.method === 'HEAD') && assetGetMatch) {
      const roomCode = sanitizeRoomCode(assetGetMatch[1]);
      const assetPath = assetGetMatch[2];
      if (!ALLOWED_ASSET_PATH.test(assetPath)) {
        res.writeHead(404, CORS_HEADERS).end();
        return;
      }
      const room = rooms.get(roomCode);
      if (!room) {
        res.writeHead(404, CORS_HEADERS).end();
        return;
      }
      const isAudio = AUDIO_ASSET_PATH.test(assetPath);
      if (isAudio && room.passwordRequired && requestUrl.searchParams.get('t') !== room.audioToken) {
        res.writeHead(403, { ...CORS_HEADERS, 'Cache-Control': 'no-store' }).end();
        return;
      }

      const cacheControl = isAudio && room.passwordRequired ? 'private, no-store'
        : assetPath.startsWith('portraits/') ? 'public, max-age=86400, immutable'
        : 'public, max-age=3600';
      const cached = room.assetCache.get(assetPath);
      if (cached) {
        serveBufferedAsset(res, req.method, req.headers.range, cached.data, cached.contentType, cacheControl);
        return;
      }

      if (!room.hostSocket || room.hostSocket.destroyed) {
        res.writeHead(503, { ...CORS_HEADERS, 'Cache-Control': 'no-store' }).end('Host offline');
        return;
      }

      let reqId = room.inFlightByPath.get(assetPath);
      let pending = reqId ? room.pendingAssets.get(reqId) : null;
      if (!pending) {
        reqId = crypto.randomBytes(12).toString('hex');
        pending = {
          path: assetPath,
          waiters: [],
          timer: setTimeout(() => failPendingAsset(room, reqId, 504, 'Host timeout'), assetTimeoutMs),
        };
        room.pendingAssets.set(reqId, pending);
        room.inFlightByPath.set(assetPath, reqId);
        sendWsText(room.hostSocket, JSON.stringify({ __relay: 'asset_req', reqId, path: assetPath }));
      }
      if (pending.waiters.length >= ASSET_WAIT_MAX_WAITERS) {
        res.writeHead(503, CORS_HEADERS).end();
        return;
      }
      const waiter = { res, method: req.method, rangeHeader: req.headers.range };
      pending.waiters.push(waiter);
      res.on('close', () => {
        const idx = pending.waiters.indexOf(waiter);
        if (idx >= 0) pending.waiters.splice(idx, 1);
      });
      return;
    }

    if ((req.method === 'GET' || req.method === 'HEAD') && hasGuestDir) {
      await serveStaticGuest(req, res, reqPath);
      return;
    }

    res.writeHead(req.method === 'GET' || req.method === 'HEAD' ? 404 : 405, CORS_HEADERS).end();
  }

  const requestHandler = (req, res) => {
    handleHttp(req, res).catch(() => {
      if (res.destroyed) return;
      if (!res.headersSent) res.writeHead(500, CORS_HEADERS).end();
      else res.destroy();
    });
  };
  const server = tls?.key && tls?.cert
    ? https.createServer({ key: tls.key, cert: tls.cert }, requestHandler)
    : http.createServer(requestHandler);
  server.requestTimeout = Math.max(20000, assetTimeoutMs + 5000);
  server.headersTimeout = 10000;

  server.on('upgrade', (req, socket) => {
    const urlObj = new URL(req.url || '/', 'http://localhost');
    if (!/\/relay\/ws$/i.test(urlObj.pathname)) {
      socket.write('HTTP/1.1 404 Not Found\r\nConnection: close\r\n\r\n');
      socket.destroy();
      return;
    }

    const wsKey = req.headers['sec-websocket-key'];
    if (!wsKey || typeof wsKey !== 'string') {
      socket.write('HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n');
      socket.destroy();
      return;
    }

    const roomCode = sanitizeRoomCode(urlObj.searchParams.get('room'));
    const role = urlObj.searchParams.get('role');
    if (roomCode.length < 4) {
      socket.write('HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\nInvalid room');
      socket.destroy();
      return;
    }

    const isHost = role === 'host';
    if (isHost) {
      const token = urlObj.searchParams.get('token') || '';
      const epoch = Number(urlObj.searchParams.get('epoch') ?? '0');
      if (!Number.isSafeInteger(epoch) || epoch < 0) {
        socket.write('HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\nInvalid generation');
        socket.destroy();
        return;
      }
      if (token.length < 16) {
        socket.write('HTTP/1.1 403 Forbidden\r\nConnection: close\r\n\r\nMissing host token');
        socket.destroy();
        return;
      }
      const existing = rooms.get(roomCode);
      if (existing && existing.hostToken !== token) {
        socket.write('HTTP/1.1 403 Forbidden\r\nConnection: close\r\n\r\nRoom owned by another host');
        socket.destroy();
        return;
      }
      if (existing && existing.transportEpoch > epoch) {
        socket.write('HTTP/1.1 409 Conflict\r\nConnection: close\r\n\r\nStale generation');
        socket.destroy();
        return;
      }
      if (!existing && rooms.size >= maxRooms) {
        socket.write('HTTP/1.1 503 Service Unavailable\r\nConnection: close\r\n\r\nRelay busy');
        socket.destroy();
        return;
      }

      const accept = crypto.createHash('sha1').update(wsKey + WS_GUID).digest('base64');
      socket.write(
        [
          'HTTP/1.1 101 Switching Protocols',
          'Upgrade: websocket',
          'Connection: Upgrade',
          `Sec-WebSocket-Accept: ${accept}`,
          '\r\n',
        ].join('\r\n'),
      );
      socket.setNoDelay(true);

      let room = existing;
      if (!room) {
        room = {
          roomCode,
          hostToken: token,
          transportEpoch: epoch,
          passwordRequired: urlObj.searchParams.get('pw') === '1',
          audioToken: urlObj.searchParams.get('at') || '',
          hostSocket: null,
          guests: new Map(),
          authenticatedPeers: new Set(),
          clientLastSeen: new Map(),
          pendingAssets: new Map(),
          inFlightByPath: new Map(),
          assetCache: createBufferLruCache(maxRoomCacheBytes),
          graceTimer: null,
        };
        rooms.set(roomCode, room);
      } else {
        room.transportEpoch = epoch;
        if (room.graceTimer) {
          clearTimeout(room.graceTimer);
          room.graceTimer = null;
        }
        room.passwordRequired = urlObj.searchParams.get('pw') === '1';
        room.audioToken = urlObj.searchParams.get('at') || '';
      }

      if (room.hostSocket && !room.hostSocket.destroyed) {
        sendWsClose(room.hostSocket);
        room.hostSocket.destroy();
      }
      room.hostSocket = socket;

      for (const peerId of room.guests.keys()) {
        sendWsText(room.hostSocket, JSON.stringify({ __relay: 'client_connected', peerId }));
      }

      attachWsFrameParser(socket, {
        onText: (raw) => {
          if (room.hostSocket !== socket) return;
          let envelope;
          try {
            envelope = JSON.parse(raw);
          } catch {
            return;
          }
          if (!envelope || typeof envelope !== 'object') return;
          if (envelope.__relay === 'auth_peer' && typeof envelope.peerId === 'string') {
            room.authenticatedPeers.add(envelope.peerId);
          } else if (envelope.__relay === 'broadcast') {
            const frame = encodeWsFrame(Buffer.from(JSON.stringify(envelope.payload), 'utf8'), 0x1);
            const isLowPriority = envelope.payload?.type === 'LATENCY';
            if (room.passwordRequired) {
              for (const peerId of [...room.authenticatedPeers]) {
                writeClientFrame(room, peerId, room.guests.get(peerId), frame, isLowPriority);
              }
            } else {
              for (const [peerId, clientSock] of [...room.guests.entries()]) {
                writeClientFrame(room, peerId, clientSock, frame, isLowPriority);
              }
            }
          } else if (envelope.__relay === 'to_client' && typeof envelope.peerId === 'string') {
            const target = room.guests.get(envelope.peerId);
            if (target) {
              const frame = encodeWsFrame(Buffer.from(JSON.stringify(envelope.payload), 'utf8'), 0x1);
              writeClientFrame(room, envelope.peerId, target, frame, false);
            }
          }
        },
      });

      const onHostGone = () => {
        if (room.hostSocket !== socket) return;
        room.hostSocket = null;
        for (const reqId of [...room.pendingAssets.keys()]) {
          failPendingAsset(room, reqId, 502, 'Host disconnected');
        }
        if (room.graceTimer) clearTimeout(room.graceTimer);
        room.graceTimer = setTimeout(() => destroyRoom(roomCode), roomGraceMs);
        if (room.graceTimer.unref) room.graceTimer.unref();
      };

      socket.on('close', onHostGone);
      socket.on('error', onHostGone);
      return;
    }

    const room = rooms.get(roomCode);
    if (!room || !room.hostSocket || room.hostSocket.destroyed) {
      socket.write('HTTP/1.1 404 Not Found\r\nConnection: close\r\n\r\nRoom unavailable');
      socket.destroy();
      return;
    }
    if (room.guests.size >= maxClientsPerRoom) {
      socket.write('HTTP/1.1 503 Service Unavailable\r\nConnection: close\r\n\r\nRoom full');
      socket.destroy();
      return;
    }

    const accept = crypto.createHash('sha1').update(wsKey + WS_GUID).digest('base64');
    socket.write(
      [
        'HTTP/1.1 101 Switching Protocols',
        'Upgrade: websocket',
        'Connection: Upgrade',
        `Sec-WebSocket-Accept: ${accept}`,
        '\r\n',
      ].join('\r\n'),
    );
    socket.setNoDelay(true);

    guestSeq += 1;
    const peerId = `r_${guestSeq}`;
    room.guests.set(peerId, socket);
    room.clientLastSeen.set(peerId, Date.now());
    if (!room.passwordRequired) room.authenticatedPeers.add(peerId);

    sendWsText(room.hostSocket, JSON.stringify({ __relay: 'client_connected', peerId }));

    attachWsFrameParser(socket, {
      onActivity: () => {
        room.clientLastSeen.set(peerId, Date.now());
      },
      onText: (raw) => {
        let payload;
        try {
          payload = JSON.parse(raw);
        } catch {
          return;
        }
        if (room.hostSocket && !room.hostSocket.destroyed) {
          sendWsText(room.hostSocket, JSON.stringify({ __relay: 'client_msg', peerId, payload }));
        }
      },
    });

    const cleanupGuest = () => {
      room.authenticatedPeers.delete(peerId);
      room.clientLastSeen.delete(peerId);
      if (!room.guests.has(peerId)) return;
      room.guests.delete(peerId);
      if (room.hostSocket && !room.hostSocket.destroyed) {
        sendWsText(room.hostSocket, JSON.stringify({ __relay: 'client_disconnected', peerId }));
      }
    };
    socket.on('close', cleanupGuest);
    socket.on('error', cleanupGuest);
  });

  return {
    async start() {
      await new Promise((resolve, reject) => {
        const onError = (err) => {
          server.removeListener('listening', onListening);
          reject(err);
        };
        const onListening = () => {
          server.removeListener('error', onError);
          resolve();
        };
        server.once('error', onError);
        server.once('listening', onListening);
        server.listen(port, host);
      });

      keepaliveTimer = setInterval(() => {
        const now = Date.now();
        for (const room of rooms.values()) {
          if (room.hostSocket && !room.hostSocket.destroyed) sendWsPing(room.hostSocket);
          for (const [peerId, sock] of [...room.guests.entries()]) {
            const lastSeen = room.clientLastSeen.get(peerId) || 0;
            if (now - lastSeen > CLIENT_IDLE_TIMEOUT_MS) {
              dropGuest(room, peerId, 'idle_timeout');
              continue;
            }
            sendWsPing(sock);
          }
        }
      }, 20000);
      if (keepaliveTimer.unref) keepaliveTimer.unref();

      const addr = server.address();
      const boundPort = typeof addr === 'object' && addr ? addr.port : port;
      const protocol = tls?.key && tls?.cert ? 'https' : 'http';
      return {
        port: boundPort,
        host,
        protocol,
        wsProtocol: protocol === 'https' ? 'wss' : 'ws',
      };
    },

    getStats() {
      return {
        rooms: rooms.size,
        guests: [...rooms.values()].reduce((sum, room) => sum + room.guests.size, 0),
      };
    },

    async stop() {
      if (keepaliveTimer) {
        clearInterval(keepaliveTimer);
        keepaliveTimer = null;
      }
      for (const roomCode of [...rooms.keys()]) {
        destroyRoom(roomCode);
      }
      staticGzipCache.clear();
      const closing = new Promise((resolve) => server.close(() => resolve()));
      server.closeAllConnections();
      await closing;
    },
  };
}

function isDirectCliRun() {
  if (!process.argv[1]) return false;
  try {
    return pathToFileURL(fs.realpathSync(process.argv[1])).href === import.meta.url;
  } catch {
    return false;
  }
}

if (isDirectCliRun()) {
  const __dirname = path.dirname(fileURLToPath(import.meta.url));
  const defaultGuestDir = ['dist-web-guest', 'web-guest'].map((folder) => path.resolve(__dirname, '..', folder)).find(fs.existsSync);
  const tls = process.env.TLS_KEY_PATH && process.env.TLS_CERT_PATH
    ? {
        key: fs.readFileSync(process.env.TLS_KEY_PATH, 'utf8'),
        cert: fs.readFileSync(process.env.TLS_CERT_PATH, 'utf8'),
      }
    : null;
  const relay = createRelayServer({
    port: Number(process.env.PORT || 8787),
    host: process.env.HOST || '0.0.0.0',
    webGuestDir: process.env.WEB_GUEST_DIR || defaultGuestDir || null,
    tls,
  });
  const info = await relay.start();
  console.log(`[karuta-relay] listening on ${info.protocol}://${info.host}:${info.port}`);
  const shutdown = () => {
    void relay.stop().then(() => process.exit(0));
  };
  process.once('SIGINT', shutdown);
  process.once('SIGTERM', shutdown);
}
