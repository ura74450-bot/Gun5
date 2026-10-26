'use strict';
/**
 * Gunshade — сервер общей игры (Node.js + ws).
 * Есть комнаты (миры): основной «Общий сервер» и пользовательские карты,
 * которые игроки загружают из редактора уровней. В каждой комнате свой мир:
 * враги, предметы, сундук, PvP и чат синхронизированы между игроками комнаты.
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const PUBLIC_DIR = path.join(__dirname, 'public');
const MAX_PLAYERS = 8;
const MAX_CUSTOM_ROOMS = 40;
const MAX_BODY = 1.5 * 1024 * 1024;
const STEP_MS = 1000 / 60;
// ----- мультиплеер-редактор -----
const MAX_EDITOR_PLAYERS = 4;
const MAX_EDITOR_ROOMS = 20;
const ED_CELL = 40;            // размер клетки редактора (как EC на клиенте)
const ED_MAX_WALLS = Infinity;     // как лимит пользовательских карт
const ED_SIZES = [1000, 2000, 3000, 5000];
const ED_TOOLS = ['wall', 'player', 'player2', 'enemy', 'chest', 'heal', 'armor', 'erase'];
const ED_BRUSH = ['wall', 'enemy', 'heal', 'armor'];

// ====================== КАРТА ПО УМОЛЧАНИЮ ======================
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
const ENEMY_CELLS = [
  [15,5],[21,5],[16,7],[20,8],[22,8],[26,8],[14,9],[10,13],
  [16,13],[21,14],[16,17],[21,18],[18,20],[26,20],[10,21],[3,22],
  [16,22],[21,22],[27,23],[16,25],[20,25],[8,27],[18,27],[27,27]
];
const ROCKET_BLAST_RADIUS = CELL * 3;

function defaultConfig() {
  const walls = [];
  for (let r = 0; r < MAP_GRID.length; r++) {
    for (let c = 0; c < MAP_GRID[r].length; c++) {
      if (MAP_GRID[r][c] === '#') walls.push({ x: c * CELL, y: r * CELL, w: CELL, h: CELL });
    }
  }
  return {
    w: MAP_GRID[0].length * CELL, h: MAP_GRID.length * CELL, walls,
    enemyPos: ENEMY_CELLS.map(([c, r]) => ({ x: (c + 0.5) * CELL, y: (r + 0.5) * CELL })),
    healPos: [{ x: 840, y: 408 }],
    armorPos: [{ x: 216, y: 600 }, { x: 456, y: 600 }],
    chestPositions: [{ x: 888, y: 408 }],
    spawns: [{ x: 168, y: 696 }]
  };
}

// ====================== ПРОВЕРКА ПОЛЬЗОВАТЕЛЬСКОГО УРОВНЯ ======================
function fin(v) { v = Number(v); return Number.isFinite(v) ? v : null; }
function cleanPoint(p, w, h) {
  if (!p || typeof p !== 'object') return null;
  const x = fin(p.x), y = fin(p.y);
  if (x === null || y === null) return null;
  return { x: Math.round(Math.max(0, Math.min(w, x)) * 10) / 10, y: Math.round(Math.max(0, Math.min(h, y)) * 10) / 10 };
}
const SPRITE_NAMES = ['wall', 'enemy', 'player', 'pistol', 'knife', 'bazooka', 'heal', 'armor', 'chest', 'bullet', 'rocket'];
function cleanSprites(raw) {
  const out = {};
  if (!raw || typeof raw !== 'object') return out;
  for (const k of SPRITE_NAMES) {
    const sp = raw[k];
    if (!sp || typeof sp !== 'object') continue;
    const w = sp.w | 0, h = sp.h | 0;
    if (w < 1 || h < 1 || w > 32 || h > 32) continue;
    if (typeof sp.d !== 'string' || sp.d.length !== w * h * 8 || !/^[0-9a-fA-F]+$/.test(sp.d)) continue;
    out[k] = { w, h, d: sp.d.toLowerCase() };
  }
  return out;
}
function sanitizeLevel(raw) {
  if (!raw || typeof raw !== 'object') throw new Error('Некорректный уровень');
  const width = fin(raw.width), height = fin(raw.height);
  if (!width || !height || width < 200 || height < 200 || width > 6000 || height > 6000) {
    throw new Error('Размер карты должен быть от 200 до 6000');
  }
  if (!Array.isArray(raw.walls)) throw new Error('В уровне нет стен');
    const walls = [];
  for (const w of raw.walls) {
    if (!w) continue;
    const x = fin(w.x), y = fin(w.y);
    if (x === null || y === null) continue;
    const ww = Math.max(1, Math.min(2000, fin(w.w) || 20));
    const hh = Math.max(1, Math.min(2000, fin(w.h) || 20));
    walls.push({ x: Math.round(x), y: Math.round(y), w: Math.round(ww), h: Math.round(hh) });
  }
  const pts = (arr, max) => (Array.isArray(arr) ? arr : []).slice(0, max).map(p => cleanPoint(p, width, height)).filter(Boolean);
  const heals = pts(Array.isArray(raw.heals) ? raw.heals : (raw.heal ? [raw.heal] : []), Infinity);
  const armors = pts(Array.isArray(raw.armors) ? raw.armors : (raw.armor ? [raw.armor] : []), Infinity);
  return {
    width: Math.round(width), height: Math.round(height), walls,
    player: cleanPoint(raw.player, width, height),
    enemies: pts(raw.enemies, Infinity),
    player2: cleanPoint(raw.player2, width, height),
    chests: pts(Array.isArray(raw.chests) ? raw.chests : (raw.chest ? [raw.chest] : []), 10),
    heals, armors,
    sprites: cleanSprites(raw.sprites)
  };
}
function configFromLevel(level) {
  return {
    w: level.width, h: level.height, walls: level.walls,
    enemyPos: level.enemies, healPos: level.heals, armorPos: level.armors,
    chestPositions: level.chests,
    spawns: level.player2
      ? [level.player || { x: level.width / 2, y: level.height / 2 }, level.player2]
      : [level.player || { x: level.width / 2, y: level.height / 2 }]
  };
}

// ====================== СЕТКА СТЕН (быстрый поиск) ======================
const GCELL = 64;
function buildGrid(walls, w, h) {
  const cols = Math.ceil(w / GCELL) + 1, rows = Math.ceil(h / GCELL) + 1;
  const cells = new Array(cols * rows);
  for (const wall of walls) {
    const x0 = Math.max(0, Math.floor(wall.x / GCELL)), x1 = Math.min(cols - 1, Math.floor((wall.x + wall.w) / GCELL));
    const y0 = Math.max(0, Math.floor(wall.y / GCELL)), y1 = Math.min(rows - 1, Math.floor((wall.y + wall.h) / GCELL));
    for (let cy = y0; cy <= y1; cy++) {
      for (let cx = x0; cx <= x1; cx++) {
        const k = cy * cols + cx;
        (cells[k] || (cells[k] = [])).push(wall);
      }
    }
  }
  return { cols, rows, cells };
}
function cellList(g, cx, cy) {
  if (cx < 0 || cy < 0 || cx >= g.cols || cy >= g.rows) return undefined;
  return g.cells[cy * g.cols + cx];
}

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
function resolveWalls(room, c) {
  const g = room.grid;
  const x0 = Math.floor((c.x - c.radius) / GCELL), x1 = Math.floor((c.x + c.radius) / GCELL);
  const y0 = Math.floor((c.y - c.radius) / GCELL), y1 = Math.floor((c.y + c.radius) / GCELL);
  for (let cy = y0; cy <= y1; cy++) {
    for (let cx = x0; cx <= x1; cx++) {
      const list = cellList(g, cx, cy);
      if (list) for (let i = 0; i < list.length; i++) resolveCircleWallCollision(c, list[i]);
    }
  }
}
function circleHitsWall(room, x, y, r) {
  const g = room.grid;
  const x0 = Math.floor((x - r) / GCELL), x1 = Math.floor((x + r) / GCELL);
  const y0 = Math.floor((y - r) / GCELL), y1 = Math.floor((y + r) / GCELL);
  for (let cy = y0; cy <= y1; cy++) {
    for (let cx = x0; cx <= x1; cx++) {
      const list = cellList(g, cx, cy);
      if (!list) continue;
      for (const w of list) {
        const px = Math.max(w.x, Math.min(x, w.x + w.w)), py = Math.max(w.y, Math.min(y, w.y + w.h));
        if (Math.hypot(x - px, y - py) < r) return true;
      }
    }
  }
  return false;
}
function isWallPoint(room, x, y) {
  const list = cellList(room.grid, Math.floor(x / GCELL), Math.floor(y / GCELL));
  if (!list) return false;
  for (let i = 0; i < list.length; i++) {
    const w = list[i];
    if (x > w.x && x < w.x + w.w && y > w.y && y < w.y + w.h) return true;
  }
  return false;
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
// обход ячеек сетки вдоль отрезка (быстро даже на больших картах)
function pathBlocked(room, x1, y1, x2, y2) {
  const g = room.grid;
  let cx = Math.floor(x1 / GCELL), cy = Math.floor(y1 / GCELL);
  const ex = Math.floor(x2 / GCELL), ey = Math.floor(y2 / GCELL);
  const dx = x2 - x1, dy = y2 - y1;
  const sx = dx > 0 ? 1 : -1, sy = dy > 0 ? 1 : -1;
  const tDx = dx !== 0 ? GCELL / Math.abs(dx) : Infinity;
  const tDy = dy !== 0 ? GCELL / Math.abs(dy) : Infinity;
  let tMaxX = dx !== 0 ? ((dx > 0 ? (cx + 1) * GCELL - x1 : x1 - cx * GCELL) / Math.abs(dx)) : Infinity;
  let tMaxY = dy !== 0 ? ((dy > 0 ? (cy + 1) * GCELL - y1 : y1 - cy * GCELL) / Math.abs(dy)) : Infinity;
  for (let guard = 0; guard < 600; guard++) {
    const list = cellList(g, cx, cy);
    if (list) for (let i = 0; i < list.length; i++) if (lineHitsWall(x1, y1, x2, y2, list[i])) return true;
    if (cx === ex && cy === ey) break;
    if (tMaxX < tMaxY) { cx += sx; tMaxX += tDx; } else { cy += sy; tMaxY += tDy; }
  }
  return false;
}

// ====================== КОМНАТЫ ======================
const rooms = new Map();
let nextId = 1;

function buildRoom({ id, name, host, level, persistent }) {
  const cfg = level ? configFromLevel(level) : defaultConfig();
  const room = {
    id, name, host: host || '', level: level || null, persistent: !!persistent, cfg,
    grid: buildGrid(cfg.walls, cfg.w, cfg.h),
    players: new Map(), // ws -> player
    chatHistory: [], pvp: false, enemyRespawn: true, allDeadTicks: 0,
    createdAt: Date.now(), emptySince: Date.now(),
    enemies: [], heals: [], armors: [], chests: [], bazooka: false, srvBullets: []
  };
  resetWorld(room);
  return room;
}
function makeRoom(opts) {
  const room = buildRoom(opts);
  rooms.set(room.id, room);
  return room;
}

function resetWorld(room) {
  const cfg = room.cfg;
  room.enemies = cfg.enemyPos.map((p, i) => ({
    id: i, x: p.x, y: p.y, radius: 16,
    hp: 3, maxHp: 3, speed: 1.2, vx: 0, vy: 0, isDead: false,
    isAlerted: false, detectionRadius: 220, attackCooldown: 0
  }));
  room.heals = cfg.healPos.map(p => ({ x: p.x, y: p.y, taken: false }));
  room.armors = cfg.armorPos.map(p => ({ x: p.x, y: p.y, taken: false }));
  room.chests = cfg.chestPositions.map(p => ({ x: p.x, y: p.y, opened: false }));
  room.bazooka = false;
  room.srvBullets = [];
  room.allDeadTicks = 0;
}

const r1 = (v) => Math.round(v * 10) / 10;
function worldData(room) {
  return {
    e: room.enemies.map(e => [e.id, r1(e.x), r1(e.y), e.hp, e.isAlerted ? 1 : 0, e.isDead ? 1 : 0]),
    h: room.heals.map(h => (h.taken ? 1 : 0)),
    a: room.armors.map(a => (a.taken ? 1 : 0)),
    c: room.chests.map(c => (c.opened ? 1 : 0))
  };
}

const SPAWN_OFFSETS = [[0, 0], [44, 0], [88, 0], [132, 0], [0, 44], [44, 44], [88, 44], [132, 44]];
function spawnFor(room, slot) {
  const spawns = room.cfg.spawns;
  const base = spawns[slot % spawns.length];
  const R = 18;
  const free = (x, y) => x > R && y > R && x < room.cfg.w - R && y < room.cfg.h - R && !circleHitsWall(room, x, y, R);
  const o = SPAWN_OFFSETS[Math.floor(slot / spawns.length) % SPAWN_OFFSETS.length];
  let x = base.x + o[0], y = base.y + o[1];
  if (free(x, y)) return { x, y };
  for (let rad = 40; rad <= 240; rad += 30) {
    for (let a = 0; a < 8; a++) {
      x = base.x + Math.cos(a * Math.PI / 4) * rad;
      y = base.y + Math.sin(a * Math.PI / 4) * rad;
      if (free(x, y)) return { x, y };
    }
  }
  return { x: base.x, y: base.y };
}
function freeSlot(room) {
  const used = new Set([...room.players.values()].map(p => p.slot));
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
function broadcast(room, obj, except) {
  const data = JSON.stringify(obj);
  for (const ws of room.players.keys()) if (ws !== except) send(ws, data);
}
function sysChat(room, text) {
  const target = room.lobby || room; // тест уровня пишет в чат всей комнаты-редактора
  target.chatHistory.push({ n: '', x: text, s: 1 });
  if (target.chatHistory.length > 30) target.chatHistory.shift();
  broadcast(target, { t: 'chat', s: 1, n: '', x: text });
}

// ====================== СИМУЛЯЦИЯ ======================
function stepBullets(room) {
  const list = room.srvBullets;
  for (let i = list.length - 1; i >= 0; i--) {
    const b = list[i];
    b.x += b.vx; b.y += b.vy; b.life--;
    if (b.life <= 0 || isWallPoint(room, b.x, b.y)) list.splice(i, 1);
  }
}

function stepEnemies(room) {
  const alive = [];
  for (const p of room.players.values()) if (p.ready && !p.dead && !p.noclip) alive.push(p);
  if (!alive.length) return;
  const enemies = room.enemies;
  const W = room.cfg.w, H = room.cfg.h;

  for (let i = 0; i < enemies.length; i++) {
    const enemy = enemies[i];
    if (enemy.isDead) continue;
    if (enemy.attackCooldown > 0) enemy.attackCooldown--;

    let target = null, distToPlayer = Infinity;
    for (const p of alive) {
      const d = Math.hypot(p.x - enemy.x, p.y - enemy.y);
      if (d < distToPlayer) { distToPlayer = d; target = p; }
    }

    if (!enemy.isAlerted) {
      if (distToPlayer <= enemy.detectionRadius) enemy.isAlerted = true;
      else { enemy.vx *= 0.5; enemy.vy *= 0.5; continue; }
    }

    let moveVx = 0, moveVy = 0;
    let desiredAngle = Math.atan2(target.y - enemy.y, target.x - enemy.x);

    if (pathBlocked(room, enemy.x, enemy.y, target.x, target.y)) {
      const rayDistance = 70;
      const rayAngles = [0.4, -0.4, 0.8, -0.8, 1.2, -1.2, 1.57, -1.57];
      for (const off of rayAngles) {
        const a = desiredAngle + off;
        if (!pathBlocked(room, enemy.x, enemy.y, enemy.x + Math.cos(a) * rayDistance, enemy.y + Math.sin(a) * rayDistance)) {
          desiredAngle = a;
          break;
        }
      }
    }
    moveVx += Math.cos(desiredAngle) * enemy.speed;
    moveVy += Math.sin(desiredAngle) * enemy.speed;

    for (const b of room.srvBullets) {
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

    resolveWalls(room, enemy);
    enemy.x = Math.max(enemy.radius, Math.min(W - enemy.radius, enemy.x));
    enemy.y = Math.max(enemy.radius, Math.min(H - enemy.radius, enemy.y));

    for (let j = i + 1; j < enemies.length; j++) {
      if (!enemies[j].isDead) resolveCircleCircleCollision(enemy, enemies[j], 0.5, 0.5);
    }

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

function stepRoom(room) {
  for (const p of room.players.values()) if (p.invuln > 0) p.invuln--;
  stepBullets(room);
  stepEnemies(room);

  if (room.enemyRespawn && room.enemies.length && room.enemies.every(e => e.isDead)) {
    room.allDeadTicks++;
    if (room.allDeadTicks >= 60 * 15) {
      resetWorld(room);
      broadcast(room, { t: 'world', world: worldData(room) });
      sysChat(room, 'Все враги побеждены! Начинается новый раунд.');
    }
  } else {
    room.allDeadTicks = 0;
  }
}

function broadcastSnapshot(room) {
  const plist = [];
  for (const p of room.players.values()) {
    if (!p.ready) continue;
    plist.push([p.id, p.slot, r1(p.x), r1(p.y), p.a, p.w, p.hp, p.ar, p.rl, p.ks, p.iv, p.dead ? 1 : 0]);
  }
  const wd = worldData(room);
  const data = JSON.stringify({ t: 'snap', p: plist, e: wd.e, h: wd.h, a: wd.a, c: wd.c, pv: room.pvp ? 1 : 0 });
  for (const ws of room.players.keys()) {
    if (ws.bufferedAmount > 256 * 1024) continue;
    send(ws, data);
  }
  // участники комнаты-редактора, которые сейчас рисуют, видят тестеров на карте
  if (room.lobby && plist.length) {
    room.snapN = (room.snapN || 0) + 1;
    if (room.snapN % 2 === 0) {
      const tp = JSON.stringify({ t: 'etp', p: plist.map(a => [a[0], a[1], a[2], a[3], a[4], a[11]]) });
      for (const m of room.lobby.players.values()) if (!m.p) send(m.ws, tp);
    }
  }
}

// ====================== КОМАНДЫ ЧАТА ======================
function runCommand(room, ws, p, text) {
  const parts = text.slice(1).toLowerCase().split(/\s+/).filter(Boolean);
  const name = 'Игрок ' + (p.slot + 1);
  if (parts[0] === 'pvp' && (parts[1] === 'on' || parts[1] === 'off')) {
    room.pvp = parts[1] === 'on';
    sysChat(room, name + (room.pvp ? ' включил PvP: игроки теперь могут наносить урон друг другу.' : ' выключил PvP.'));
  } else if (parts[0] === 'enemy' && parts[1] === 'kill') {
    const ids = [];
    for (const e of room.enemies) {
      if (e.isDead) continue;
      e.hp = 0; e.isDead = true; e.vx = 0; e.vy = 0;
      ids.push(e.id);
    }
    broadcast(room, { t: 'ekill', k: ids });
    sysChat(room, name + ' убил всех врагов (' + ids.length + ').');
  } else if (parts[0] === 'enemy' && parts[1] === 'respawn' && (parts[2] === 'on' || parts[2] === 'off')) {
    room.enemyRespawn = parts[2] === 'on';
    room.allDeadTicks = 0;
    sysChat(room, name + (room.enemyRespawn
      ? ' включил возрождение врагов: когда все враги убиты, начнётся новый раунд.'
      : ' выключил возрождение врагов: новый раунд не начнётся.'));
  } else if (parts[0] === 'shield' && parts[1] === 'set') {
    broadcast(room, { t: 'shield' });
    sysChat(room, name + ' выдал всем игрокам щит.');
  } else if (parts[0] === 'noclip' && (parts[1] === 'on' || parts[1] === 'off')) {
    p.noclip = parts[1] === 'on';
    send(ws, { t: 'mode', noclip: p.noclip, god: p.god });
    sysChat(room, name + (p.noclip ? ' включил noclip: нет коллизии, быстрый бег, мобы не атакуют.' : ' выключил noclip.'));
  } else if (parts[0] === 'infinity' && ['heat', 'heart', 'health', 'hp'].includes(parts[1]) && (parts[2] === 'on' || parts[2] === 'off')) {
    p.god = parts[2] === 'on';
    send(ws, { t: 'mode', noclip: p.noclip, god: p.god });
    sysChat(room, name + (p.god ? ' включил бесконечные жизни.' : ' выключил бесконечные жизни.'));
  } else if (parts[0] === 'reload' && room.lobby) {
    reloadTest(room, name);
  } else {
    send(ws, { t: 'chat', s: 1, n: '', x: 'Команды: /pvp on|off, /enemy kill, /enemy respawn on|off, /shield set, /noclip on|off, /infinity heat on|off' + (room.lobby ? ', /reload (обновить тест под текущий уровень)' : '') });
  }
}

// ====================== ОБРАБОТКА СООБЩЕНИЙ ======================
function handleMessage(ws, p, m) {
  const room = p.room;
  switch (m.t) {
    case 's': {
      p.x = num(m.x, 0, room.cfg.w, p.x);
      p.y = num(m.y, 0, room.cfg.h, p.y);
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
      if (rocket && !room.bazooka) break;
      p.lastShot = now;
      const ang = Math.atan2(Number(m.vy) || 0, Number(m.vx) || 0);
      const speed = rocket ? 8.5 : 12;
      const out = {
        t: 'shoot', id: p.id, r: rocket ? 1 : 0, bid: num(m.bid, 0, 1e9, 0),
        x: num(m.x, 0, room.cfg.w, p.x), y: num(m.y, 0, room.cfg.h, p.y),
        vx: Math.cos(ang) * speed, vy: Math.sin(ang) * speed
      };
      if (room.srvBullets.length < 300) {
        room.srvBullets.push({ x: out.x, y: out.y, vx: out.vx, vy: out.vy, life: rocket ? 240 : 120, owner: p.id, bid: out.bid });
      }
      if (!rocket) {
        for (const e of room.enemies) {
          if (!e.isDead && !e.isAlerted && Math.hypot(p.x - e.x, p.y - e.y) < 350) e.isAlerted = true;
        }
      }
      broadcast(room, out, ws);
      break;
    }
    case 'hit': {
      if (p.dead) break;
      const e = room.enemies[m.id | 0];
      if (!e || e.isDead) break;
      const ang = num(m.ang, -10, 10, 0);
      const kind = m.kind === 'knife' ? 'knife' : 'bullet';
      const bid = num(m.bid, 0, 1e9, 0);
      if (kind === 'knife') {
        if (Math.hypot(p.x - e.x, p.y - e.y) > 200) break;
        e.hp -= e.maxHp * 0.5;
      } else {
        e.hp -= 1;
        e.vx += Math.cos(ang) * 6.8;
        e.vy += Math.sin(ang) * 6.8;
        room.srvBullets = room.srvBullets.filter(b => !(b.owner === p.id && b.bid === bid));
      }
      e.isAlerted = true;
      let dead = false;
      if (e.hp <= 0) { e.hp = 0; e.isDead = true; e.vx = 0; e.vy = 0; dead = true; }
      broadcast(room, { t: 'ehit', id: e.id, hp: e.hp, kind, ang, dead, by: p.id, bid });
      break;
    }
    case 'phit': {
      if (!room.pvp || p.dead) break;
      let target = null;
      for (const q of room.players.values()) if (q.id === (m.id | 0)) target = q;
      if (!target || target === p || target.dead || !target.ready) break;
      const kind = m.kind === 'knife' ? 'knife' : 'bullet';
      if (kind === 'knife' && Math.hypot(p.x - target.x, p.y - target.y) > 200) break;
      const bid = num(m.bid, 0, 1e9, 0);
      if (kind === 'bullet') room.srvBullets = room.srvBullets.filter(b => !(b.owner === p.id && b.bid === bid));
      broadcast(room, { t: 'phit', id: target.id, by: p.id, bid, kind, ang: num(m.ang, -10, 10, 0) });
      break;
    }
    case 'boom': {
      const now = Date.now();
      if (!room.bazooka || p.dead || now - p.lastBoom < 250) break;
      p.lastBoom = now;
      const x = num(m.x, 0, room.cfg.w, p.x), y = num(m.y, 0, room.cfg.h, p.y);
      const bid = num(m.bid, 0, 1e9, 0);
      const killed = [];
      for (const e of room.enemies) {
        if (e.isDead) continue;
        if (Math.hypot(e.x - x, e.y - y) <= ROCKET_BLAST_RADIUS + e.radius) {
          e.hp = 0; e.isDead = true; e.vx = 0; e.vy = 0;
          killed.push(e.id);
        }
      }
      room.srvBullets = room.srvBullets.filter(b => !(b.owner === p.id && b.bid === bid));
      broadcast(room, { t: 'boom', x, y, k: killed, by: p.id, bid });
      if (room.pvp) {
        for (const q of room.players.values()) {
          if (q === p || q.dead || !q.ready) continue;
          if (Math.hypot(q.x - x, q.y - y) <= ROCKET_BLAST_RADIUS + q.radius) {
            broadcast(room, { t: 'phit', id: q.id, by: p.id, bid: 0, kind: 'rocket', ang: Math.atan2(q.y - y, q.x - x) });
          }
        }
      }
      break;
    }
    case 'pickup': {
      if (p.dead) break;
      const i = m.i | 0;
      let item = null;
      if (m.k === 'heal') item = room.heals[i];
      else if (m.k === 'armor') item = room.armors[i];
      else if (m.k === 'chest') item = room.chests[i];
      if (!item) break;
      if (Math.hypot(p.x - item.x, p.y - item.y) > 220) break;
      if (m.k === 'chest') {
        if (item.opened) break;
        item.opened = true;
        const first = !room.bazooka;
        room.bazooka = true;
        broadcast(room, { t: 'pick', k: 'chest', i, by: p.id });
        sysChat(room, 'Игрок ' + (p.slot + 1) + (first ? ' открыл сундук — базуку получили все!' : ' открыл ещё один сундук.'));
      } else {
        if (item.taken) break;
        item.taken = true;
        broadcast(room, { t: 'pick', k: m.k, i, by: p.id });
      }
      break;
    }
    case 'respawn': {
      p.dead = false;
      p.invuln = 60;
      const sp = spawnFor(room, p.slot);
      p.x = sp.x; p.y = sp.y;
      send(ws, { t: 'spawn', x: sp.x, y: sp.y });
      break;
    }
    case 'chat': {
      const now = Date.now();
      if (now - p.lastChat < 600) break;
      const text = String(m.text || '').replace(/[\u0000-\u001f\u007f]/g, ' ').trim().slice(0, 200);
      if (!text) break;
      p.lastChat = now;
      if (text[0] === '/') { runCommand(room, ws, p, text); break; }
      const name = 'Игрок ' + (p.slot + 1);
      room.chatHistory.push({ n: name, x: text, s: 0 });
      if (room.chatHistory.length > 30) room.chatHistory.shift();
      broadcast(room, { t: 'chat', id: p.id, n: name, x: text, s: 0 });
      break;
    }
    case 'ping':
      send(ws, { t: 'pong', ts: num(m.ts, 0, 1e15, 0) });
      break;
  }
}

// ====================== МУЛЬТИПЛЕЕР-РЕДАКТОР ======================
// Комната-редактор: до 4 человек правят один уровень. Правки (стены, объекты, спрайты)
// применяются на сервере и рассылаются остальным. Любой участник может войти в «тест уровня» —
// это обычный серверный мир (враги, PvP, команды чата) на снимке текущего уровня;
// остальные видят тестера на карте редактора. Чат общий; команды работают только в тесте.
function edSnap(v, max) { return Math.max(0, Math.min(max - ED_CELL, Math.floor(v / ED_CELL) * ED_CELL)); }

function makeEditorRoom({ id, name, host, size, level }) {
  const L = level
    ? {
        width: level.width, height: level.height, player: level.player, player2: level.player2,
        enemies: level.enemies.slice(), chests: level.chests.slice(0, 2), heals: level.heals.slice(), armors: level.armors.slice(),
        sprites: Object.assign({}, level.sprites)
      }
    : { width: size, height: size, player: { x: 100, y: 100 }, player2: null, enemies: [], chests: [], heals: [], armors: [], sprites: {} };
  const room = {
    kind: 'editor', id, name, host: host || '', persistent: false, level: L,
    wallMap: new Map(), players: new Map(), chatHistory: [], game: null, version: 0,
    createdAt: Date.now(), emptySince: Date.now(), token: ''
  };
  if (level) for (const w of level.walls) room.wallMap.set(w.x + ',' + w.y, { x: w.x, y: w.y, w: ED_CELL, h: ED_CELL });
  rooms.set(id, room);
  return room;
}

// Применить одну операцию редактора (зеркало клиентской edApplyOp)
function edPlaceOne(room, tool, x, y) {
  const L = room.level, EC = ED_CELL, cx = x + EC / 2, cy = y + EC / 2;
  const at = (p) => !!p && Math.floor(p.x / EC) * EC === x && Math.floor(p.y / EC) * EC === y;
  if (tool === 'wall') {
    const k = x + ',' + y;
    if (!room.wallMap.has(k) && room.wallMap.size < ED_MAX_WALLS) room.wallMap.set(k, { x, y, w: EC, h: EC });
  } else if (tool === 'player') L.player = { x: cx, y: cy };
  else if (tool === 'player2') L.player2 = { x: cx, y: cy };
  else if (tool === 'enemy') { if (!L.enemies.some(at)) L.enemies.push({ x: cx, y: cy }); }
  else if (tool === 'chest') {
    if (!L.chests.some(at)) { if (L.chests.length >= 2) L.chests.shift(); L.chests.push({ x: cx, y: cy }); }
  } else if (tool === 'heal') { if (!L.heals.some(at)) L.heals.push({ x: cx, y: cy }); }
  else if (tool === 'armor') { if (!L.armors.some(at)) L.armors.push({ x: cx, y: cy }); }
}
function edApply(room, tool, x, y, n) {
  const L = room.level, EC = ED_CELL, W = L.width, H = L.height;
  x = edSnap(x, W); y = edSnap(y, H);
  const off = Math.floor((n - 1) / 2) * EC;
  const rx = x - off, ry = y - off, size = n * EC;
  if (tool === 'erase') {
    for (let yy = ry; yy < ry + size; yy += EC) for (let xx = rx; xx < rx + size; xx += EC) room.wallMap.delete(xx + ',' + yy);
    const inRect = (p) => {
      const cx = Math.floor(p.x / EC) * EC, cy = Math.floor(p.y / EC) * EC;
      return cx >= rx && cx < rx + size && cy >= ry && cy < ry + size;
    };
    L.enemies = L.enemies.filter(p => !inRect(p));
    L.chests = L.chests.filter(p => !inRect(p));
    L.heals = L.heals.filter(p => !inRect(p));
    L.armors = L.armors.filter(p => !inRect(p));
    if (L.player && inRect(L.player)) L.player = null;
    if (L.player2 && inRect(L.player2)) L.player2 = null;
  } else if (ED_BRUSH.includes(tool) && n > 1) {
    for (let yy = ry; yy < ry + size; yy += EC) {
      for (let xx = rx; xx < rx + size; xx += EC) {
        if (xx < 0 || yy < 0 || xx + EC > W || yy + EC > H) continue;
        edPlaceOne(room, tool, xx, yy);
      }
    }
  } else edPlaceOne(room, tool, x, y);
}

// Контрольная сумма уровня (одинаковая функция на клиенте) — чтобы заметить расхождение и пересинхронизироваться
function edHash(L, walls) {
  const pt = (x, y, k) => Math.imul(((Math.round(x) * 31 + Math.round(y) * 17 + k) | 0) ^ 0x5bd1e995, 2654435761) | 0;
  let h = 0;
  for (const w of walls) h = (h + pt(w.x, w.y, 1)) | 0;
  const list = (arr, k) => { let s = arr.length * 977 + k; for (const p of arr) s = (s + pt(p.x, p.y, k)) | 0; return s | 0; };
  h = (h + list(L.enemies, 2) + list(L.chests, 3) + list(L.heals, 4) + list(L.armors, 5)) | 0;
  if (L.player) h = (h + pt(L.player.x, L.player.y, 6)) | 0;
  if (L.player2) h = (h + pt(L.player2.x, L.player2.y, 7)) | 0;
  for (const name of Object.keys(L.sprites)) {
    const d = L.sprites[name].d;
    let f = 2166136261;
    for (let i = 0; i < d.length; i++) f = Math.imul(f ^ d.charCodeAt(i), 16777619);
    h = (h + f + name.length * 131) | 0;
  }
  return h | 0;
}

function edLevelOut(room) {
  const L = room.level, wf = [];
  for (const w of room.wallMap.values()) wf.push(w.x, w.y);
  return {
    width: L.width, height: L.height, wf, player: L.player, player2: L.player2,
    enemies: L.enemies, chests: L.chests, heals: L.heals, armors: L.armors, sprites: L.sprites
  };
}
function edLevelForGame(room) {
  const L = room.level;
  return {
    width: L.width, height: L.height, walls: [...room.wallMap.values()],
    player: L.player, player2: L.player2, enemies: L.enemies, chests: L.chests, heals: L.heals, armors: L.armors, sprites: L.sprites
  };
}
function edMembers(room) {
  return [...room.players.values()].map(m => ({ id: m.id, s: m.slot, t: m.p ? 1 : 0 }));
}
function edBroadcastMembers(room) { broadcast(room, { t: 'emem', m: edMembers(room) }); }

function testInit(game, p) {
  return {
    t: 'init', id: p.id, slot: p.slot, spawn: { x: p.x, y: p.y }, pvp: game.pvp,
    room: { id: game.lobby.id, name: game.lobby.name }, level: game.level, world: worldData(game),
    chat: game.lobby.chatHistory.slice(-20), test: 1
  };
}
function newTester(game, mem) {
  const sp = spawnFor(game, mem.slot);
  return {
    ws: mem.ws, room: game, id: mem.id, slot: mem.slot, x: sp.x, y: sp.y, a: 0, w: 'pistol', hp: 100, ar: 0, rl: 0, ks: 0, iv: 0,
    dead: false, ready: false, radius: 18, invuln: 60, noclip: false, god: false,
    lastShot: 0, lastBoom: 0, lastChat: 0, tokens: 120, tokenTime: Date.now()
  };
}

function startTest(room, mem) {
  if (mem.p) return;
  if (!room.game) {
    let lvl;
    try { lvl = sanitizeLevel(edLevelForGame(room)); }
    catch (e) { send(mem.ws, { t: 'chat', s: 1, n: '', x: 'Не удалось запустить тест: ' + e.message }); return; }
    const game = buildRoom({ id: room.id + '-test', name: room.name, host: '', level: lvl, persistent: false });
    game.lobby = room;
    game.version = room.version;
    room.game = game;
  }
  const game = room.game;
  const p = newTester(game, mem);
  game.players.set(mem.ws, p);
  mem.p = p;
  send(mem.ws, testInit(game, p));
  if (game.version !== room.version) {
    send(mem.ws, { t: 'chat', s: 1, n: '', x: 'Тест запущен на версии уровня до последних правок. Команда /reload обновит его для всех тестеров.' });
  }
  edBroadcastMembers(room);
  sysChat(room, 'Игрок ' + (mem.slot + 1) + ' вошёл в тест уровня');
}

function leaveTest(room, mem, notify) {
  const p = mem.p;
  if (!p) return;
  const game = p.room;
  game.players.delete(mem.ws);
  game.srvBullets = game.srvBullets.filter(b => b.owner !== p.id);
  mem.p = null;
  if (game.players.size === 0 && room.game === game) room.game = null;
  if (notify) send(mem.ws, { t: 'eback' });
  edBroadcastMembers(room);
  sysChat(room, 'Игрок ' + (mem.slot + 1) + ' вышел из теста уровня');
}

// /reload — пересобрать тест из текущего уровня редактора
function reloadTest(game, byName) {
  const room = game.lobby;
  let lvl;
  try { lvl = sanitizeLevel(edLevelForGame(room)); }
  catch (e) { sysChat(game, 'Не удалось обновить тест: ' + e.message); return; }
  game.level = lvl;
  game.cfg = configFromLevel(lvl);
  game.grid = buildGrid(game.cfg.walls, game.cfg.w, game.cfg.h);
  game.version = room.version;
  resetWorld(game);
  for (const p of game.players.values()) {
    const sp = spawnFor(game, p.slot);
    p.x = sp.x; p.y = sp.y; p.dead = false; p.invuln = 60; p.ready = false; p.hp = 100;
    send(p.ws, testInit(game, p));
  }
  sysChat(game, byName + ' обновил тест: загружена текущая версия уровня.');
}

function handleEditorMessage(ws, mem, m) {
  const room = mem.room, L = room.level;
  switch (m.t) {
    case 'eo': { // пачка правок: [[инструмент, x, y, размер кисти], ...]
      if (!Array.isArray(m.ops)) break;
      const ops = [];
      for (const o of m.ops.slice(0, 300)) {
        if (!Array.isArray(o)) continue;
        const ti = o[0] | 0, tool = ED_TOOLS[ti];
        const x = Number(o[1]), y = Number(o[2]);
        if (!tool || !Number.isFinite(x) || !Number.isFinite(y)) continue;
        if (x < -ED_CELL || y < -ED_CELL || x > L.width || y > L.height) continue;
        const n = Math.max(1, Math.min(5, o[3] | 0 || 1));
        edApply(room, tool, x, y, n);
        ops.push([ti, Math.round(x), Math.round(y), n]);
      }
      if (ops.length) {
        room.version++;
        broadcast(room, { t: 'eo', id: mem.id, ops }, ws);
      }
      break;
    }
    case 'esp': { // спрайт-текстура (null — вернуть стандартную)
      const name = String(m.n || '');
      if (!SPRITE_NAMES.includes(name)) break;
      if (m.s === null) {
        delete L.sprites[name];
      } else {
        const sp = cleanSprites({ [name]: m.s })[name];
        if (!sp) break;
        L.sprites[name] = sp;
      }
      room.version++;
      broadcast(room, { t: 'esp', id: mem.id, n: name, s: m.s === null ? null : L.sprites[name] }, ws);
      break;
    }
    case 'ecur': {
      const now = Date.now();
      if (now - mem.lastCur < 50) break;
      mem.lastCur = now;
      if (m.x === null || m.x === undefined) { broadcast(room, { t: 'ecur', id: mem.id, x: null }, ws); break; }
      broadcast(room, {
        t: 'ecur', id: mem.id, x: num(m.x, 0, L.width, 0), y: num(m.y, 0, L.height, 0),
        n: num(m.n, 1, 5, 1) | 0, k: num(m.k, 0, 7, 0) | 0
      }, ws);
      break;
    }
    case 'esync': {
      const now = Date.now();
      if (now - (mem.lastSync || 0) < 2000) break;
      mem.lastSync = now;
      send(ws, { t: 'elevel', level: edLevelOut(room) });
      break;
    }
    case 'chat': {
      const now = Date.now();
      if (now - mem.lastChat < 600) break;
      const text = String(m.text || '').replace(/[\u0000-\u001f\u007f]/g, ' ').trim().slice(0, 200);
      if (!text) break;
      mem.lastChat = now;
      if (text[0] === '/') {
        if (mem.p) runCommand(mem.p.room, ws, mem.p, text);
        else send(ws, { t: 'chat', s: 1, n: '', x: 'Команды работают только в тесте уровня. Нажмите «ТЕСТ УРОВНЯ», чтобы зайти в тест.' });
        break;
      }
      const name = 'Игрок ' + (mem.slot + 1);
      room.chatHistory.push({ n: name, x: text, s: 0 });
      if (room.chatHistory.length > 30) room.chatHistory.shift();
      broadcast(room, { t: 'chat', id: mem.id, n: name, x: text, s: 0 });
      break;
    }
    case 'etest': startTest(room, mem); break;
    case 'eleave': leaveTest(room, mem, true); break;
    case 'ping': send(ws, { t: 'pong', ts: num(m.ts, 0, 1e15, 0) }); break;
    default:
      // игровые сообщения (позиция, выстрелы, подбор…) — только пока участник в тесте
      if (mem.p && ['s', 'shoot', 'hit', 'phit', 'boom', 'pickup', 'respawn'].includes(m.t)) handleMessage(ws, mem.p, m);
  }
}

function connectEditor(ws, room) {
  if (room.players.size >= MAX_EDITOR_PLAYERS) { send(ws, { t: 'full', max: MAX_EDITOR_PLAYERS }); ws.close(); return; }
  const used = new Set([...room.players.values()].map(m => m.slot));
  let slot = 0;
  while (used.has(slot)) slot++;
  const mem = {
    ws, room, id: nextId++, slot, p: null, lastChat: 0, lastCur: 0, lastSync: 0, tokens: 120, tokenTime: Date.now()
  };
  room.players.set(ws, mem);
  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });

  send(ws, {
    t: 'einit', id: mem.id, slot, room: { id: room.id, name: room.name, max: MAX_EDITOR_PLAYERS },
    level: edLevelOut(room), members: edMembers(room), chat: room.chatHistory.slice(-20)
  });
  edBroadcastMembers(room);
  sysChat(room, 'Игрок ' + (slot + 1) + ' зашёл в комнату');

  ws.on('message', (raw) => {
    const now = Date.now();
    mem.tokens = Math.min(120, mem.tokens + (now - mem.tokenTime) * 0.08);
    mem.tokenTime = now;
    if (mem.tokens < 1) return;
    mem.tokens -= 1;
    let m;
    try { m = JSON.parse(raw.toString()); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;
    try { handleEditorMessage(ws, mem, m); } catch (e) { console.error('editor msg error', e); }
  });
  const cleanup = () => {
    if (!room.players.has(ws)) return;
    if (mem.p) {
      const game = mem.p.room;
      game.players.delete(ws);
      game.srvBullets = game.srvBullets.filter(b => b.owner !== mem.p.id);
      if (game.players.size === 0 && room.game === game) room.game = null;
      mem.p = null;
    }
    room.players.delete(ws);
    if (room.players.size === 0) room.emptySince = Date.now();
    broadcast(room, { t: 'ecur', id: mem.id, x: null });
    edBroadcastMembers(room);
    sysChat(room, 'Игрок ' + (slot + 1) + ' вышел из комнаты');
  };
  ws.on('close', cleanup);
  ws.on('error', () => { try { ws.terminate(); } catch (e) {} cleanup(); });
}

function listEditors() {
  return [...rooms.values()].filter(r => r.kind === 'editor')
    .sort((a, b) => b.createdAt - a.createdAt)
    .map(r => ({
      id: r.id, name: r.name, host: r.host, players: r.players.size, max: MAX_EDITOR_PLAYERS,
      testing: r.game ? r.game.players.size : 0, walls: r.wallMap.size, w: r.level.width, h: r.level.height
    }));
}

// ====================== HTTP (статика + API карт) ======================
const MIME = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8', '.json': 'application/json',
  '.png': 'image/png', '.jpg': 'image/jpeg', '.svg': 'image/svg+xml',
  '.ico': 'image/x-icon', '.webp': 'image/webp'
};

function json(res, code, obj) {
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}
function cleanText(v, max, def) {
  const s = String(v == null ? '' : v).replace(/[\u0000-\u001f\u007f<>]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, max);
  return s || def;
}
function readBody(req, res, cb) {
  let size = 0; const chunks = []; let aborted = false;
  req.on('data', (c) => {
    if (aborted) return;
    size += c.length;
    if (size > MAX_BODY) { aborted = true; json(res, 413, { error: 'Файл уровня слишком большой (максимум ~1.5 МБ)' }); req.destroy(); return; }
    chunks.push(c);
  });
  req.on('end', () => { if (!aborted) cb(Buffer.concat(chunks).toString('utf8')); });
  req.on('error', () => {});
}

const hostLog = new Map(); // ip -> [timestamps]
function hostAllowed(ip) {
  const now = Date.now();
  const arr = (hostLog.get(ip) || []).filter(t => now - t < 60000);
  if (arr.length >= 6) { hostLog.set(ip, arr); return false; }
  arr.push(now); hostLog.set(ip, arr);
  return true;
}

function listMaps() {
  return [...rooms.values()].filter(r => !r.persistent && r.kind !== 'editor')
    .sort((a, b) => b.createdAt - a.createdAt)
    .map(r => ({
      id: r.id, name: r.name, host: r.host, players: r.players.size, max: MAX_PLAYERS,
      enemies: r.cfg.enemyPos.length, walls: r.cfg.walls.length, w: r.cfg.w, h: r.cfg.h, created: r.createdAt
    }));
}

function removeRoom(room, reason) {
  rooms.delete(room.id);
  if (room.game) room.game.players.clear();
  for (const ws of [...room.players.keys()]) {
    send(ws, { t: 'noroom', reason });
    try { ws.close(); } catch (e) {}
  }
  room.players.clear();
}

function handleApi(req, res, pathname) {
  if (pathname === '/api/maps' && req.method === 'GET') return json(res, 200, { maps: listMaps() });

  if (pathname === '/api/maps' && req.method === 'POST') {
    const ip = String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
    if (!hostAllowed(ip)) return json(res, 429, { error: 'Слишком часто. Подождите минуту.' });
    return readBody(req, res, (body) => {
      let data;
      try { data = JSON.parse(body); } catch (e) { return json(res, 400, { error: 'Некорректный JSON' }); }
      let level;
      try { level = sanitizeLevel(data && data.level); } catch (e) { return json(res, 400, { error: e.message }); }
      const name = cleanText(data.name, 30, '');
      if (!name) return json(res, 400, { error: 'Введите название мира' });

      const custom = [...rooms.values()].filter(r => !r.persistent && r.kind !== 'editor');
      if (custom.length >= MAX_CUSTOM_ROOMS) {
        const empty = custom.filter(r => r.players.size === 0).sort((a, b) => a.emptySince - b.emptySince)[0];
        if (!empty) return json(res, 503, { error: 'На сервере слишком много активных карт. Попробуйте позже.' });
        removeRoom(empty, 'Карта удалена (освобождено место)');
      }
      const id = crypto.randomBytes(4).toString('hex');
      const token = crypto.randomBytes(12).toString('hex');
      const room = makeRoom({ id, name, host: cleanText(data.host, 20, 'Аноним'), level, persistent: false });
      room.token = token;
      return json(res, 200, { id: room.id, token });
    });
  }

  // ----- мультиплеер-редактор -----
  if (pathname === '/api/editors' && req.method === 'GET') return json(res, 200, { rooms: listEditors() });

  if (pathname === '/api/editors' && req.method === 'POST') {
    const ip = String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
    if (!hostAllowed(ip)) return json(res, 429, { error: 'Слишком часто. Подождите минуту.' });
    return readBody(req, res, (body) => {
      let data;
      try { data = JSON.parse(body); } catch (e) { return json(res, 400, { error: 'Некорректный JSON' }); }
      data = data || {};
      const name = cleanText(data.name, 30, '');
      if (!name) return json(res, 400, { error: 'Введите название комнаты' });
      let size = Number(data.size) || 2000;
      let level = null;
      if (data.level) {
        try { level = sanitizeLevel(data.level); } catch (e) { return json(res, 400, { error: e.message }); }
        const bad = level.walls.some(w => w.x % ED_CELL !== 0 || w.y % ED_CELL !== 0 || w.w !== ED_CELL || w.h !== ED_CELL);
        if (bad) return json(res, 400, { error: 'Стены этого уровня не по сетке редактора 40×40 — его нельзя загрузить в комнату.' });
      } else if (!ED_SIZES.includes(size)) {
        return json(res, 400, { error: 'Допустимый размер карты: ' + ED_SIZES.join(', ') });
      }
      const eds = [...rooms.values()].filter(r => r.kind === 'editor');
      if (eds.length >= MAX_EDITOR_ROOMS) {
        const empty = eds.filter(r => r.players.size === 0).sort((a, b) => a.emptySince - b.emptySince)[0];
        if (!empty) return json(res, 503, { error: 'Слишком много активных комнат. Попробуйте позже.' });
        removeRoom(empty, 'Комната удалена (освобождено место)');
      }
      const id = 'e' + crypto.randomBytes(4).toString('hex');
      const room = makeEditorRoom({ id, name, host: cleanText(data.host, 20, 'Аноним'), size, level });
      room.token = crypto.randomBytes(12).toString('hex');
      return json(res, 200, { id: room.id, token: room.token });
    });
  }
  const em = pathname.match(/^\/api\/editors\/(e[a-f0-9]+)$/);
  if (em && req.method === 'DELETE') {
    const room = rooms.get(em[1]);
    if (!room || room.kind !== 'editor') return json(res, 404, { error: 'Комната не найдена' });
    if (req.headers['x-token'] !== room.token) return json(res, 403, { error: 'Нет прав на удаление' });
    removeRoom(room, 'Комната удалена хостом');
    return json(res, 200, { ok: true });
  }

  const m = pathname.match(/^\/api\/maps\/([a-f0-9]+)$/);
  if (m && req.method === 'DELETE') {
    const room = rooms.get(m[1]);
    if (!room || room.persistent) return json(res, 404, { error: 'Карта не найдена' });
    if (req.headers['x-token'] !== room.token) return json(res, 403, { error: 'Нет прав на удаление' });
    removeRoom(room, 'Карта удалена хостом');
    return json(res, 200, { ok: true });
  }
  return json(res, 404, { error: 'Not found' });
}

const server = http.createServer((req, res) => {
  let pathname;
  try { pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname); }
  catch (e) { res.writeHead(400); return res.end('Bad request'); }

  if (pathname === '/health') {
    res.writeHead(200, { 'Content-Type': 'text/plain' });
    return res.end('ok');
  }
  if (pathname.startsWith('/api/')) {
    try { return handleApi(req, res, pathname); } catch (e) { console.error(e); return json(res, 500, { error: 'Ошибка сервера' }); }
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

// ====================== WebSocket ======================
const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 32768, perMessageDeflate: false });

wss.on('connection', (ws, req) => {
  let roomId = 'main';
  try { roomId = new URL(req.url, 'http://localhost').searchParams.get('room') || 'main'; } catch (e) {}
  const room = rooms.get(roomId);
  if (!room) { send(ws, { t: 'noroom', reason: 'Карта не найдена или удалена' }); ws.close(); return; }

  if (room.kind === 'editor') { connectEditor(ws, room); return; }

  const slot = freeSlot(room);
  if (slot < 0) { send(ws, { t: 'full' }); ws.close(); return; }

  const sp = spawnFor(room, slot);
  const p = {
    ws, room, id: nextId++, slot, x: sp.x, y: sp.y, a: 0, w: 'pistol', hp: 100, ar: 0, rl: 0, ks: 0, iv: 0,
    dead: false, ready: false, radius: 18, invuln: 60, noclip: false, god: false,
    lastShot: 0, lastBoom: 0, lastChat: 0, tokens: 120, tokenTime: Date.now()
  };
  room.players.set(ws, p);
  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });

  send(ws, {
    t: 'init', id: p.id, slot, spawn: sp, pvp: room.pvp, room: { id: room.id, name: room.name },
    level: room.level, world: worldData(room), chat: room.chatHistory.slice(-20)
  });
  sysChat(room, 'Игрок ' + (slot + 1) + ' зашёл в игру');

  ws.on('message', (raw) => {
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
    if (!room.players.has(ws)) return;
    room.players.delete(ws);
    room.srvBullets = room.srvBullets.filter(b => b.owner !== p.id);
    if (room.players.size === 0) room.emptySince = Date.now();
    sysChat(room, 'Игрок ' + (slot + 1) + ' вышел из игры');
  };
  ws.on('close', cleanup);
  ws.on('error', () => { try { ws.terminate(); } catch (e) {} cleanup(); });
});

setInterval(() => {
  for (const ws of wss.clients) {
    if (ws.isAlive === false) { ws.terminate(); continue; }
    ws.isAlive = false;
    try { ws.ping(); } catch (e) {}
  }
}, 15000);

// удаляем давно пустые пользовательские карты (6 часов без игроков)
setInterval(() => {
  const now = Date.now();
  for (const room of [...rooms.values()]) {
    if (!room.persistent && room.players.size === 0 && now - room.emptySince > 6 * 3600 * 1000) removeRoom(room, 'Карта удалена по таймауту');
  }
}, 60000);

// контрольные суммы уровней — клиенты сверяют и при расхождении запрашивают полную синхронизацию
setInterval(() => {
  for (const room of rooms.values()) {
    if (room.kind !== 'editor' || room.players.size === 0) continue;
    broadcast(room, { t: 'esum', h: edHash(room.level, room.wallMap.values()) });
  }
}, 5000);

// ====================== ИГРОВОЙ ЦИКЛ ======================
makeRoom({ id: 'main', name: 'Общий сервер', level: null, persistent: true });

let last = Date.now(), acc = 0, tick = 0;
setInterval(() => {
  const now = Date.now();
  acc += now - last;
  last = now;
  const active = [];
  for (const room of rooms.values()) {
    if (room.kind === 'editor') { if (room.game && room.game.players.size > 0) active.push(room.game); }
    else if (room.players.size > 0) active.push(room);
  }
  if (!active.length) { acc = 0; return; }
  if (acc > 250) acc = 250;
  while (acc >= STEP_MS) {
    for (const room of active) {
      try { stepRoom(room); } catch (e) { console.error('step error', e); }
    }
    acc -= STEP_MS;
    tick++;
    if (tick % 3 === 0) for (const room of active) broadcastSnapshot(room);
  }
}, 8);

process.on('uncaughtException', (e) => console.error('uncaught', e));
process.on('unhandledRejection', (e) => console.error('unhandled', e));

server.listen(PORT, '0.0.0.0', () => console.log('Gunshade server on port ' + PORT));
const shutdown = () => { try { wss.close(); server.close(() => process.exit(0)); } catch (e) { process.exit(0); } setTimeout(() => process.exit(0), 3000); };
process.on('SIGTERM', shutdown);
process.on('SIGINT', shutdown);
