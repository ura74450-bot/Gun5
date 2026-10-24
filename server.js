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
  if (raw.walls.length > 8000) throw new Error('Слишком много стен (максимум 8000)');
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
  const heals = pts(Array.isArray(raw.heals) ? raw.heals : (raw.heal ? [raw.heal] : []), 40);
  const armors = pts(Array.isArray(raw.armors) ? raw.armors : (raw.armor ? [raw.armor] : []), 40);
  return {
    width: Math.round(width), height: Math.round(height), walls,
    player: cleanPoint(raw.player, width, height),
    enemies: pts(raw.enemies, 80),
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

function makeRoom({ id, name, host, level, persistent }) {
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
  rooms.set(id, room);
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
  room.chatHistory.push({ n: '', x: text, s: 1 });
  if (room.chatHistory.length > 30) room.chatHistory.shift();
  broadcast(room, { t: 'chat', s: 1, n: '', x: text });
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
  for (const p of room.players.values()) if (p.ready && !p.dead) alive.push(p);
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
  } else {
    send(ws, { t: 'chat', s: 1, n: '', x: 'Команды: /pvp on, /pvp off, /enemy kill, /enemy respawn on, /enemy respawn off' });
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
  return [...rooms.values()].filter(r => !r.persistent)
    .sort((a, b) => b.createdAt - a.createdAt)
    .map(r => ({
      id: r.id, name: r.name, host: r.host, players: r.players.size, max: MAX_PLAYERS,
      enemies: r.cfg.enemyPos.length, walls: r.cfg.walls.length, w: r.cfg.w, h: r.cfg.h, created: r.createdAt
    }));
}

function removeRoom(room, reason) {
  rooms.delete(room.id);
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

      const custom = [...rooms.values()].filter(r => !r.persistent);
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
const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 8192, perMessageDeflate: false });

wss.on('connection', (ws, req) => {
  let roomId = 'main';
  try { roomId = new URL(req.url, 'http://localhost').searchParams.get('room') || 'main'; } catch (e) {}
  const room = rooms.get(roomId);
  if (!room) { send(ws, { t: 'noroom', reason: 'Карта не найдена или удалена' }); ws.close(); return; }

  const slot = freeSlot(room);
  if (slot < 0) { send(ws, { t: 'full' }); ws.close(); return; }

  const sp = spawnFor(room, slot);
  const p = {
    ws, room, id: nextId++, slot, x: sp.x, y: sp.y, a: 0, w: 'pistol', hp: 100, ar: 0, rl: 0, ks: 0, iv: 0,
    dead: false, ready: false, radius: 18, invuln: 60,
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

// ====================== ИГРОВОЙ ЦИКЛ ======================
makeRoom({ id: 'main', name: 'Общий сервер', level: null, persistent: true });

let last = Date.now(), acc = 0, tick = 0;
setInterval(() => {
  const now = Date.now();
  acc += now - last;
  last = now;
  const active = [];
  for (const room of rooms.values()) if (room.players.size > 0) active.push(room);
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
