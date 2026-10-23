'use strict';
/**
 * Gunshade — сервер общей игры (Node.js + ws).
 * Один общий мир: враги, предметы и сундук синхронизированы между всеми игроками.
 * Сервер владеет врагами (ИИ, здоровье, урон по игрокам) и предметами.
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const PUBLIC_DIR = path.join(__dirname, 'public');
const MAX_PLAYERS = 8;
const STEP_MS = 1000 / 60;

// ====================== КАРТА (как в игре) ======================
const CELL = 48;
const MAP_GRID = [
  '................................',
  '................................',
  '............#################...',
  '............#################...',
  '............##         ##  ##...',
  '............## E     E ##  ##...',
  '............##         ##  ##...',
  '............##  E      ##  ##...',
  '............##    CCE E## E##...',
  '##############E   CC   ## E##...',
  '###############   #######  ##...',
  '##    ##    ###   #######  ##...',
  '##  A ##    ##         ##  ##...',
  '##        E ##  E      ##  ####.',
  '## S        ##       E ##  ####.',
  '##          ##         ##    ##.',
  '##    ##    ##         ##    ##.',
  '##    ##    ##  E      ##    ##.',
  '########    ##       E ##    ##.',
  '########    ##         ##    ##.',
  '##          ##    E    ## E  ##.',
  '##        E ##         ##    ##.',
  '## E        ##  E    E ##    ##.',
  '##          ##         ##  E ##.',
  '###   ########               ##.',
  '###   ########  E   E        ##.',
  '##                           ##.',
  '##      E         E    ## E ##..',
  '##                     ##    ##.',
  '###############################.',
  '###############################.',
  '................................'
];
const MAP_W = MAP_GRID[0].length * CELL;
const MAP_H = MAP_GRID.length * CELL;

const walls = [];
for (let r = 0; r < MAP_GRID.length; r++) {
  for (let c = 0; c < MAP_GRID[r].length; c++) {
    if (MAP_GRID[r][c] === '#') walls.push({ x: c * CELL, y: r * CELL, w: CELL, h: CELL });
  }
}
function isWallAt(x, y) {
  const c = Math.floor(x / CELL), r = Math.floor(y / CELL);
  const row = MAP_GRID[r];
  return !!row && row[c] === '#';
}

const ENEMY_CELLS = [
  [15,5],[21,5],[16,7],[20,8],[22,8],[26,8],[14,9],[10,13],
  [16,13],[21,14],[16,17],[21,18],[18,20],[26,20],[10,21],[3,22],
  [16,22],[21,22],[27,23],[16,25],[20,25],[8,27],[18,27],[27,27]
];
const ROCKET_BLAST_RADIUS = CELL * 3;

// ====================== ФИЗИКА (порт из игры) ======================
function resolveCircleWallCollision(circle, wall) {
  const closestX = Math.max(wall.x, Math.min(circle.x, wall.x + wall.w));
  const closestY = Math.max(wall.y, Math.min(circle.y, wall.y + wall.h));
  const distX = circle.x - closestX;
  const distY = circle.y - closestY;
  const distance = Math.sqrt(distX * distX + distY * distY);
  if (distance < circle.radius) {
    const overlap = circle.radius - distance;
    if (distance === 0) circle.x += overlap;
    else {
      circle.x += (distX / distance) * overlap;
      circle.y += (distY / distance) * overlap;
    }
  }
}

function resolveCircleCircleCollision(c1, c2, r1, r2) {
  const dx = c2.x - c1.x, dy = c2.y - c1.y;
  const dist = Math.sqrt(dx * dx + dy * dy);
  const minDist = c1.radius + c2.radius;
  if (dist < minDist && dist > 0) {
    const overlap = minDist - dist;
    const nx = dx / dist, ny = dy / dist;
    c1.x -= nx * overlap * r1; c1.y -= ny * overlap * r1;
    c2.x += nx * overlap * r2; c2.y += ny * overlap * r2;
  }
}

function lineHitsWall(x1, y1, x2, y2, wall) {
  const left = wall.x, right = wall.x + wall.w, top = wall.y, bottom = wall.y + wall.h;
  if (Math.max(x1, x2) < left || Math.min(x1, x2) > right || Math.max(y1, y2) < top || Math.min(y1, y2) > bottom) return false;
  const lines = [
    [left, top, right, top], [right, top, right, bottom],
    [right, bottom, left, bottom], [left, bottom, left, top]
  ];
  for (const l of lines) {
    const den = ((x2 - x1) * (l[3] - l[1])) - ((y2 - y1) * (l[2] - l[0]));
    if (den === 0) continue;
    const ua = (((l[2] - l[0]) * (y1 - l[1])) - ((l[3] - l[1]) * (x1 - l[0]))) / den;
    const ub = (((x2 - x1) * (y1 - l[1])) - ((y2 - y1) * (x1 - l[0]))) / den;
    if (ua >= 0 && ua <= 1 && ub >= 0 && ub <= 1) return true;
  }
  return false;
}
function pathBlocked(x1, y1, x2, y2) {
  for (let i = 0; i < walls.length; i++) if (lineHitsWall(x1, y1, x2, y2, walls[i])) return true;
  return false;
}

// ====================== МИР ======================
let enemies = [];
let heals = [];
let armors = [];
let chest = { x: 888, y: 408, opened: false };
let srvBullets = []; // нужны только для уклонения врагов
let allDeadTicks = 0;

function resetWorld() {
  enemies = ENEMY_CELLS.map(([c, r], i) => ({
    id: i, x: (c + 0.5) * CELL, y: (r + 0.5) * CELL, radius: 16,
    hp: 3, maxHp: 3, speed: 1.2, vx: 0, vy: 0, isDead: false,
    isAlerted: false, detectionRadius: 220, attackCooldown: 0
  }));
  heals = [{ x: 840, y: 408, taken: false }];
  armors = [{ x: 216, y: 600, taken: false }];
  chest = { x: 888, y: 408, opened: false };
  srvBullets = [];
  allDeadTicks = 0;
}
resetWorld();

const r1 = (v) => Math.round(v * 10) / 10;
function worldData() {
  return {
    e: enemies.map(e => [e.id, r1(e.x), r1(e.y), e.hp, e.isAlerted ? 1 : 0, e.isDead ? 1 : 0]),
    h: heals.map(h => (h.taken ? 1 : 0)),
    a: armors.map(a => (a.taken ? 1 : 0)),
    c: chest.opened ? 1 : 0
  };
}

// ====================== ИГРОКИ ======================
const players = new Map(); // ws -> player
let nextId = 1;
const chatHistory = [];

function spawnFor(slot) {
  return { x: 168 + 44 * (slot % 4), y: 696 + 44 * (Math.floor(slot / 4) % 2) };
}
function freeSlot() {
  const used = new Set([...players.values()].map(p => p.slot));
  for (let i = 0; i < MAX_PLAYERS; i++) if (!used.has(i)) return i;
  return -1;
}
function num(v, min, max, def) {
  v = Number(v);
  if (!Number.isFinite(v)) return def;
  return Math.max(min, Math.min(max, v));
}

function send(ws, obj) {
  if (ws.readyState === 1) {
    try { ws.send(typeof obj === 'string' ? obj : JSON.stringify(obj)); } catch (e) {}
  }
}
function broadcast(obj, except) {
  const data = JSON.stringify(obj);
  for (const ws of players.keys()) if (ws !== except) send(ws, data);
}
function sysChat(text) {
  const msg = { t: 'chat', s: 1, n: '', x: text };
  chatHistory.push({ n: '', x: text, s: 1 });
  if (chatHistory.length > 30) chatHistory.shift();
  broadcast(msg);
}

// ====================== СИМУЛЯЦИЯ ВРАГОВ ======================
function stepBullets() {
  for (let i = srvBullets.length - 1; i >= 0; i--) {
    const b = srvBullets[i];
    b.x += b.vx; b.y += b.vy; b.life--;
    if (b.life <= 0 || isWallAt(b.x, b.y)) srvBullets.splice(i, 1);
  }
}

function stepEnemies() {
  const alive = [];
  for (const p of players.values()) if (p.ready && !p.dead) alive.push(p);

  for (let i = 0; i < enemies.length; i++) {
    const enemy = enemies[i];
    if (enemy.isDead) continue;
    if (enemy.attackCooldown > 0) enemy.attackCooldown--;

    let target = null, distToPlayer = Infinity;
    for (const p of alive) {
      const d = Math.hypot(p.x - enemy.x, p.y - enemy.y);
      if (d < distToPlayer) { distToPlayer = d; target = p; }
    }
    if (!target) { enemy.vx *= 0.5; enemy.vy *= 0.5; continue; }

    if (!enemy.isAlerted) {
      if (distToPlayer <= enemy.detectionRadius) enemy.isAlerted = true;
      else { enemy.vx *= 0.5; enemy.vy *= 0.5; continue; }
    }

    let moveVx = 0, moveVy = 0;
    let desiredAngle = Math.atan2(target.y - enemy.y, target.x - enemy.x);

    if (pathBlocked(enemy.x, enemy.y, target.x, target.y)) {
      const rayDistance = 70;
      const rayAngles = [0.4, -0.4, 0.8, -0.8, 1.2, -1.2, 1.57, -1.57];
      for (const off of rayAngles) {
        const a = desiredAngle + off;
        if (!pathBlocked(enemy.x, enemy.y, enemy.x + Math.cos(a) * rayDistance, enemy.y + Math.sin(a) * rayDistance)) {
          desiredAngle = a;
          break;
        }
      }
    }
    moveVx += Math.cos(desiredAngle) * enemy.speed;
    moveVy += Math.sin(desiredAngle) * enemy.speed;

    // уклонение от пуль (как в оригинале)
    for (const b of srvBullets) {
      const bDx = enemy.x - b.x, bDy = enemy.y - b.y;
      const bDist = Math.sqrt(bDx * bDx + bDy * bDy);
      if (bDist < 160 && bDist > 0) {
        const sp = Math.sqrt(b.vx * b.vx + b.vy * b.vy);
        const dot = (b.vx * bDx + b.vy * bDy) / (sp * bDist);
        if (dot > 0.6) {
          const perp = Math.atan2(b.vy, b.vx) + Math.PI / 2;
          const side = ((enemy.x - b.x) * b.vy - (enemy.y - b.y) * b.vx) > 0 ? 1 : -1;
          moveVx += Math.cos(perp) * 3.5 * side;
          moveVy += Math.sin(perp) * 3.5 * side;
        }
      }
    }

    enemy.vx += (moveVx - enemy.vx) * 0.25;
    enemy.vy += (moveVy - enemy.vy) * 0.25;
    enemy.x += enemy.vx;
    enemy.y += enemy.vy;

    for (let w = 0; w < walls.length; w++) resolveCircleWallCollision(enemy, walls[w]);
    enemy.x = Math.max(enemy.radius, Math.min(MAP_W - enemy.radius, enemy.x));
    enemy.y = Math.max(enemy.radius, Math.min(MAP_H - enemy.radius, enemy.y));

    for (let j = i + 1; j < enemies.length; j++) {
      if (!enemies[j].isDead) resolveCircleCircleCollision(enemy, enemies[j], 0.5, 0.5);
    }

    // контакт с игроками
    for (const p of alive) {
      const d = Math.hypot(p.x - enemy.x, p.y - enemy.y);
      if (d < enemy.radius + p.radius) {
        resolveCircleCircleCollision({ x: p.x, y: p.y, radius: p.radius }, enemy, 0, 0.8);
        if (enemy.attackCooldown <= 0 && p.invuln <= 0) {
          p.invuln = 20;
          enemy.attackCooldown = 60;
          send(p.ws, { t: 'hurt', vx: r1(enemy.vx), vy: r1(enemy.vy) });
        }
      }
    }
  }
}

function stepWorld() {
  for (const p of players.values()) if (p.invuln > 0) p.invuln--;
  stepBullets();
  stepEnemies();

  // новый раунд, когда все враги убиты
  if (enemies.length && enemies.every(e => e.isDead)) {
    allDeadTicks++;
    if (allDeadTicks >= 60 * 15) {
      resetWorld();
      broadcast({ t: 'world', world: worldData() });
      sysChat('Все враги побеждены! Начинается новый раунд.');
    }
  } else {
    allDeadTicks = 0;
  }
}

function broadcastSnapshot() {
  const plist = [];
  for (const p of players.values()) {
    if (!p.ready) continue;
    plist.push([p.id, p.slot, r1(p.x), r1(p.y), p.a, p.w, p.hp, p.ar, p.rl, p.ks, p.iv, p.dead ? 1 : 0]);
  }
  const wd = worldData();
  const data = JSON.stringify({ t: 'snap', p: plist, e: wd.e, h: wd.h, a: wd.a, c: wd.c });
  for (const ws of players.keys()) {
    if (ws.bufferedAmount > 256 * 1024) continue; // медленный клиент — пропускаем кадр
    send(ws, data);
  }
}

// ====================== ОБРАБОТКА СООБЩЕНИЙ ======================
function handleMessage(ws, p, m) {
  switch (m.t) {
    case 's': {
      p.x = num(m.x, 0, MAP_W, p.x);
      p.y = num(m.y, 0, MAP_H, p.y);
      p.a = num(m.a, -10, 10, p.a);
      p.w = (m.w === 'knife' || m.w === 'bazooka') ? m.w : 'pistol';
      p.hp = num(m.hp, -1000, 1000, p.hp);
      p.ar = num(m.ar, 0, 10, 0);
      p.rl = m.rl ? 1 : 0;
      p.ks = num(m.ks, 0, 60, 0);
      p.iv = num(m.iv, 0, 120, 0);
      p.dead = !!m.d;
      p.ready = true;
      break;
    }
    case 'shoot': {
      const now = Date.now();
      const rocket = !!m.r;
      if (now - p.lastShot < (rocket ? 300 : 100)) break;
      if (rocket && !chest.opened) break;
      p.lastShot = now;
      const ang = Math.atan2(Number(m.vy) || 0, Number(m.vx) || 0);
      const speed = rocket ? 8.5 : 12;
      const out = {
        t: 'shoot', id: p.id, r: rocket ? 1 : 0, bid: num(m.bid, 0, 1e9, 0),
        x: num(m.x, 0, MAP_W, p.x), y: num(m.y, 0, MAP_H, p.y),
        vx: Math.cos(ang) * speed, vy: Math.sin(ang) * speed
      };
      if (srvBullets.length < 300) {
        srvBullets.push({ x: out.x, y: out.y, vx: out.vx, vy: out.vy, life: rocket ? 240 : 120, owner: p.id, bid: out.bid });
      }
      if (!rocket) {
        for (const e of enemies) {
          if (!e.isDead && !e.isAlerted && Math.hypot(p.x - e.x, p.y - e.y) < 350) e.isAlerted = true;
        }
      }
      broadcast(out, ws);
      break;
    }
    case 'hit': {
      if (p.dead) break;
      const e = enemies[m.id | 0];
      if (!e || e.isDead) break;
      const ang = num(m.ang, -10, 10, 0);
      const kind = m.kind === 'knife' ? 'knife' : 'bullet';
      const bid = num(m.bid, 0, 1e9, 0);
      if (kind === 'knife') {
        if (Math.hypot(p.x - e.x, p.y - e.y) > 200) break; // слишком далеко для ножа
        e.hp -= e.maxHp * 0.5;
      } else {
        e.hp -= 1;
        e.vx += Math.cos(ang) * 6.8;
        e.vy += Math.sin(ang) * 6.8;
        srvBullets = srvBullets.filter(b => !(b.owner === p.id && b.bid === bid));
      }
      e.isAlerted = true;
      let dead = false;
      if (e.hp <= 0) { e.hp = 0; e.isDead = true; e.vx = 0; e.vy = 0; dead = true; }
      broadcast({ t: 'ehit', id: e.id, hp: e.hp, kind, ang, dead, by: p.id, bid });
      break;
    }
    case 'boom': {
      const now = Date.now();
      if (!chest.opened || p.dead || now - p.lastBoom < 250) break;
      p.lastBoom = now;
      const x = num(m.x, 0, MAP_W, p.x), y = num(m.y, 0, MAP_H, p.y);
      const bid = num(m.bid, 0, 1e9, 0);
      const killed = [];
      for (const e of enemies) {
        if (e.isDead) continue;
        if (Math.hypot(e.x - x, e.y - y) <= ROCKET_BLAST_RADIUS + e.radius) {
          e.hp = 0; e.isDead = true; e.vx = 0; e.vy = 0;
          killed.push(e.id);
        }
      }
      srvBullets = srvBullets.filter(b => !(b.owner === p.id && b.bid === bid));
      broadcast({ t: 'boom', x, y, k: killed, by: p.id, bid });
      break;
    }
    case 'pickup': {
      if (p.dead) break;
      const i = m.i | 0;
      let item = null;
      if (m.k === 'heal') item = heals[i];
      else if (m.k === 'armor') item = armors[i];
      else if (m.k === 'chest') item = chest;
      if (!item) break;
      if (Math.hypot(p.x - item.x, p.y - item.y) > 220) break;
      if (m.k === 'chest') {
        if (chest.opened) break;
        chest.opened = true;
        broadcast({ t: 'pick', k: 'chest', i: 0, by: p.id });
        sysChat('Игрок ' + (p.slot + 1) + ' открыл сундук — базуку получили все!');
      } else {
        if (item.taken) break;
        item.taken = true;
        broadcast({ t: 'pick', k: m.k, i, by: p.id });
      }
      break;
    }
    case 'respawn': {
      p.dead = false;
      p.invuln = 60;
      const sp = spawnFor(p.slot);
      p.x = sp.x; p.y = sp.y;
      send(ws, { t: 'spawn', x: sp.x, y: sp.y });
      break;
    }
    case 'chat': {
      const now = Date.now();
      if (now - p.lastChat < 600) break;
      let text = String(m.text || '').replace(/[\u0000-\u001f\u007f]/g, ' ').trim().slice(0, 200);
      if (!text) break;
      p.lastChat = now;
      const name = 'Игрок ' + (p.slot + 1);
      chatHistory.push({ n: name, x: text, s: 0 });
      if (chatHistory.length > 30) chatHistory.shift();
      broadcast({ t: 'chat', id: p.id, n: name, x: text, s: 0 });
      break;
    }
    case 'ping':
      send(ws, { t: 'pong', ts: num(m.ts, 0, 1e15, 0) });
      break;
  }
}

// ====================== HTTP + WebSocket ======================
const MIME = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8', '.json': 'application/json',
  '.png': 'image/png', '.jpg': 'image/jpeg', '.svg': 'image/svg+xml',
  '.ico': 'image/x-icon', '.webp': 'image/webp'
};

const server = http.createServer((req, res) => {
  let pathname;
  try { pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname); }
  catch (e) { res.writeHead(400); return res.end('Bad request'); }

  if (pathname === '/health') {
    res.writeHead(200, { 'Content-Type': 'text/plain' });
    return res.end('ok');
  }
  if (pathname === '/') pathname = '/index.html';
  const file = path.normalize(path.join(PUBLIC_DIR, pathname));
  if (!file.startsWith(PUBLIC_DIR)) { res.writeHead(403); return res.end('Forbidden'); }

  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404, { 'Content-Type': 'text/plain' }); return res.end('Not found'); }
    const ext = path.extname(file).toLowerCase();
    res.writeHead(200, {
      'Content-Type': MIME[ext] || 'application/octet-stream',
      'Cache-Control': ext === '.html' ? 'no-cache' : 'public, max-age=3600'
    });
    res.end(data);
  });
});

const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 8192, perMessageDeflate: false });

wss.on('connection', (ws) => {
  const slot = freeSlot();
  if (slot < 0) {
    send(ws, { t: 'full' });
    ws.close();
    return;
  }
  const sp = spawnFor(slot);
  const p = {
    ws, id: nextId++, slot, x: sp.x, y: sp.y, a: 0, w: 'pistol', hp: 100, ar: 0, rl: 0, ks: 0, iv: 0,
    dead: false, ready: false, radius: 18, invuln: 60,
    lastShot: 0, lastBoom: 0, lastChat: 0, tokens: 120, tokenTime: Date.now()
  };
  players.set(ws, p);
  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });

  send(ws, { t: 'init', id: p.id, slot, spawn: sp, world: worldData(), chat: chatHistory.slice(-20) });
  sysChat('Игрок ' + (slot + 1) + ' зашёл в игру');

  ws.on('message', (raw) => {
    // ограничение частоты сообщений (защита от флуда)
    const now = Date.now();
    p.tokens = Math.min(120, p.tokens + (now - p.tokenTime) * 0.08);
    p.tokenTime = now;
    if (p.tokens < 1) return;
    p.tokens -= 1;
    let m;
    try { m = JSON.parse(raw.toString()); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;
    try { handleMessage(ws, p, m); } catch (e) { console.error('msg error', e); }
  });

  const cleanup = () => {
    if (!players.has(ws)) return;
    players.delete(ws);
    srvBullets = srvBullets.filter(b => b.owner !== p.id);
    sysChat('Игрок ' + (slot + 1) + ' вышел из игры');
  };
  ws.on('close', cleanup);
  ws.on('error', () => { try { ws.terminate(); } catch (e) {} cleanup(); });
});

// проверка живых соединений
setInterval(() => {
  for (const ws of wss.clients) {
    if (ws.isAlive === false) { ws.terminate(); continue; }
    ws.isAlive = false;
    try { ws.ping(); } catch (e) {}
  }
}, 15000);

// игровой цикл: фиксированный шаг 60 Гц, снимок мира 20 Гц
let last = Date.now(), acc = 0, tick = 0;
setInterval(() => {
  const now = Date.now();
  acc += now - last;
  last = now;
  if (players.size === 0) { acc = 0; return; } // пустой сервер не нагружаем
  if (acc > 250) acc = 250;
  while (acc >= STEP_MS) {
    try { stepWorld(); } catch (e) { console.error('step error', e); }
    acc -= STEP_MS;
    tick++;
    if (tick % 3 === 0) broadcastSnapshot();
  }
}, 8);

process.on('uncaughtException', (e) => console.error('uncaught', e));
process.on('unhandledRejection', (e) => console.error('unhandled', e));

server.listen(PORT, '0.0.0.0', () => console.log('Gunshade server on port ' + PORT));
const shutdown = () => { try { wss.close(); server.close(() => process.exit(0)); } catch (e) { process.exit(0); } setTimeout(() => process.exit(0), 3000); };
process.on('SIGTERM', shutdown);
process.on('SIGINT', shutdown);
