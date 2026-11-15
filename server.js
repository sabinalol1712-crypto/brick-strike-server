'use strict';
// =============================================================================================
// Brick Strike 2.7: сервер сетевой игры (командный бой с ботами, закладка бомбы, рейтинг 2×2, пати).
// Нужен только Node.js 14 или новее, сторонних пакетов нет.
//
//   Запуск:   node server.js
//   Порт:     переменная PORT (по умолчанию 3100)
//   Проверка: открой в браузере  http://АДРЕС_СЕРВЕРА:3100/
//
// Сервер ведёт комнаты, здоровье, счёт, раунды с бомбой и рейтинг. Каждый игрок сам двигает своего
// бойца и сам сообщает о попаданиях, а сервер считает урон по своей таблице оружия и не даёт
// стрелять быстрее, чем может ствол. Оружие поделено по сторонам, как в CS: урон из чужого ствола
// (АК-47 у спецназа, M4 у террористов) сервер не засчитывает. Рейтинг меняется только в матчах
// «Рейтинг 2×2» между живыми игроками и лежит в файле ratings.json рядом с сервером.
//
// С версии 2.6:
//   Боты. В командном бою сервер добирает каждую команду ботами (переменная BOTS, по умолчанию до 5
//   бойцов; 0 выключает), когда в комнате двое живых игроков или когда одиночка попросил начать бой.
//   Заходит человек: бот его команды уходит. Ботов ведёт игра одного из игроков («хозяин»): она
//   считает их движение и стрельбу и сообщает серверу, а здоровье, счёт и возрождение ботов ведёт
//   сервер, как у людей. Хозяин вышел или завис: ботов подхватывает игра другого игрока.
//   Пати. Игроки с общим кодом пати попадают в одну комнату и в одну команду.
//
// С версии 2.7:
//   Карта «Старый город» стала в полтора раза больше: точка A на новом месте, раунд с бомбой идёт 115 секунд.
//   Игра старше 2.7 на этот сервер не заходит (у неё другая карта), ей пишется, что нужно обновление.
//   Оружие на земле. У убитого выпадает ствол, который был в руках, вместе со скином. Сервер помнит, где он
//   лежит, и отдаёт его первому, кто попросил, стоя рядом; подобранный ствол чужой стороны наносит урон.
//   Своё оружие игрок может выбросить сам, чтобы его взял друг.
//   «Сейчас играют». Игра в меню получает список общих боёв, где есть люди, и может зайти в выбранный.
//   Перчатки админа. Их видно у других только тогда, когда игра владельца назвала серверу его ключ.
// =============================================================================================
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

function envInt(name, lo, hi, def) { const v = parseInt(process.env[name], 10); return isFinite(v) ? Math.max(lo, Math.min(hi, v)) : def; }
const PORT = envInt('PORT', 1, 65535, 3100);
const KILL_LIMIT = envInt('KILLS', 5, 500, 50);          // до скольки убийств идёт матч
const MATCH_MS = envInt('MINUTES', 2, 60, 10) * 60000;   // сколько минут длится матч
const ROOM_SIZE = envInt('ROOM_SIZE', 2, 16, 10);        // игроков в одной комнате
const MAX_ROOMS = 40, MAX_CONN = 200, MAX_FRAME = 2048;
const FAST = process.env.BS_TEST_FAST === '1' ? 0.1 : (parseFloat(process.env.BS_TEST_FAST) > 0 ? Math.min(1, parseFloat(process.env.BS_TEST_FAST)) : 1);      // только для проверок: раунды короче
const TICK_MS = 50, RESPAWN_MS = envInt('BS_TEST_RESPAWN', 500, 60000, 3000), PROTECT_MS = 2000, POST_MS = 12000, IDLE_MS = 15000;      // (возрождение через 3 секунды; переменная только для проверок)
const VERSION = 2;
const MIN_BUILD = 27;         // с какой сборки игры пускать: 27 это версия 2.7, где карта «Старый город» стала в полтора раза больше (у старой игры другая карта: стены не совпадут)
const MAP_VER = 2;            // какую карту «Старый город» знает сервер: игра 2.7 не зайдёт на сервер, который этого числа не называет
const BOT_TEAM = envInt('BOTS', 0, 8, 5);                // до скольки бойцов боты добирают каждую команду в командном бою (0: без ботов)
const BOT_BUILD = 26;         // с какой сборки игра умеет вести ботов
const DROP_MS = 25000, DROP_ROUND_MS = 120000, DROP_MAX = 40;      // сколько лежит выпавшее оружие (в бою с возрождением; в раундах оно лежит до конца раунда) и сколько его может лежать в одной комнате
function dropLife(room) { return room.mode === 'bomb' ? DROP_ROUND_MS : DROP_MS; }
const ADMIN_KEY = 1859455190; // число, которое игра владельца получает из его секретного кода (сам код здесь не хранится)
const BOT_DMG = 0.75;         // урон от ботов немного слабее
const HOST_LAG_MS = 3500;     // хозяин ботов молчит дольше: ботов берёт другой игрок
const BOT_NAMES = ['Барс', 'Беркут', 'Волк', 'Ворон', 'Гранит', 'Гром', 'Кедр', 'Кобра', 'Орёл', 'Рысь', 'Скиф', 'Сокол', 'Тайга', 'Тень', 'Шторм', 'Ястреб', 'Байкал', 'Буран', 'Вихрь', 'Зубр'];
// раунды с бомбой: до скольки побед, сколько длятся закладка, разминирование, фитиль, раунд, заморозка перед раундом
const NEED = envInt('ROUNDS', 2, 16, 5), PLANT_MS = 3200 * FAST, DEFUSE_MS = 6000 * FAST, FUSE_MS = 40000 * FAST, ROUND_MS = 115000 * FAST, FREEZE_MS = 6000 * FAST, ROUND_POST_MS = 5000 * FAST;
// взрыв бомбы (2.9): полная сила у бомбы, дальше плавно слабее. Ближе примерно 560 единиц не выживает никто (без брони около 650),
// ранит до края радиуса, стены не защищают. Игра считает так же
const BOMB_RADIUS = 1100, BOMB_POWER = 650, BOMB_SPREAD = 340;
function bombDamage(d) { return d >= BOMB_RADIUS ? 0 : BOMB_POWER * Math.exp(-d * d / (2 * BOMB_SPREAD * BOMB_SPREAD)); }
const BOMB_ZONE = { town: [-96, 1008, 384, 1440] };         // точка A на карте «Старый город»: x от и до, z от и до
const RATE_FILE = process.env.RATINGS || path.join(__dirname, 'ratings.json');
const UID_RE = /^[a-z0-9]{16,32}$/;

// оружие: [урон, доля урона на каждые 500 единиц пути, доля сквозь броню, пауза между выстрелами в мс, дробин]
const WEAPONS = {
  glock18: [30, 0.85, 0.47, 150, 1],
  usp: [35, 0.91, 0.505, 170, 1],
  p2000: [35, 0.91, 0.505, 170, 1],
  p228: [38, 0.9, 0.64, 150, 1],
  fiveseven: [32, 0.81, 0.91, 150, 1],
  tec9: [33, 0.79, 0.906, 120, 1],
  cz75: [31, 0.85, 0.776, 100, 1],
  elite: [38, 0.79, 0.575, 120, 1],
  deagle: [53, 0.93, 0.932, 225, 1],
  mac10: [29, 0.8, 0.575, 75, 1],
  tmp: [26, 0.87, 0.6, 70, 1],
  mp7: [29, 0.85, 0.625, 80, 1],
  mp5: [27, 0.85, 0.625, 80, 1],
  ump45: [35, 0.75, 0.65, 90, 1],
  p90: [26, 0.86, 0.69, 70, 1],
  bizon: [27, 0.8, 0.575, 80, 1],
  m3: [26, 0.7, 0.5, 882, 9],
  xm1014: [20, 0.7, 0.8, 351, 6],
  sawedoff: [32, 0.45, 0.75, 845, 8],
  mag7: [30, 0.45, 0.75, 845, 8],
  galil: [30, 0.98, 0.775, 90, 1],
  famas: [30, 0.96, 0.7, 90, 1],
  ak47: [36, 0.98, 0.775, 100, 1],
  m4a4: [33, 0.97, 0.7, 90, 1],
  m4a1: [38, 0.99, 0.7, 100, 1],
  sg552: [30, 0.98, 1, 110, 1],
  aug: [28, 0.98, 0.9, 100, 1],
  scout: [88, 0.98, 0.85, 1250, 1],
  awp: [115, 0.99, 0.975, 1463, 1],
  g3sg1: [80, 0.98, 0.825, 250, 1],
  sg550: [80, 0.98, 0.825, 250, 1],
  m249: [32, 0.97, 0.8, 80, 1],
  negev: [35, 0.97, 0.75, 75, 1]
};
// оружие одной стороны: остальное из таблицы выше есть у обеих
const SIDE = { glock18: 't', tec9: 't', mac10: 't', sawedoff: 't', galil: 't', ak47: 't', sg552: 't', g3sg1: 't',
  usp: 'ct', p2000: 'ct', fiveseven: 'ct', tmp: 'ct', mag7: 'ct', famas: 'ct', m4a4: 'ct', m4a1: 'ct', aug: 'ct', sg550: 'ct' };
const W_IDS = Object.keys(WEAPONS);                     // оружие по номеру: в том же порядке его знает игра
const KNIFE_DMG = [40, 90, 65, 180];                    // взмах, взмах в спину, укол, укол в спину
const KNIFE_AP = 0.6;
const HIT_MULT = [1, 4, 1, 1.25, 0.75];                 // 1 голова, 2 грудь, 3 живот, 4 ноги

const rooms = new Map();
const conns = new Set();

function log() { const a = Array.prototype.slice.call(arguments); a.unshift(new Date().toISOString().slice(0, 19).replace('T', ' ')); console.log.apply(console, a); }
function num(v, lo, hi, def) { return typeof v === 'number' && isFinite(v) ? Math.max(lo, Math.min(hi, v)) : def; }
function cleanName(v) { const s = String(v == null ? '' : v).replace(/[\u0000-\u001f\u007f<>&"'`\\]/g, '').replace(/\s+/g, ' ').trim().slice(0, 14); return s || 'Игрок'; }
function cleanChat(v) { return String(v == null ? '' : v).replace(/[\u0000-\u001f\u007f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 80); }
function cleanRoom(v) { const s = String(v == null ? '' : v).toLowerCase().replace(/[^a-z0-9а-яё_-]/g, '').slice(0, 16); return s || 'public'; }

// ---- WebSocket: рукопожатие и кадры (RFC 6455), без сторонних пакетов -------------------------
function frame(text) {
  const data = Buffer.from(text, 'utf8'), n = data.length; let head;
  if (n < 126) head = Buffer.from([0x81, n]);
  else if (n < 65536) { head = Buffer.allocUnsafe(4); head[0] = 0x81; head[1] = 126; head.writeUInt16BE(n, 2); }
  else { head = Buffer.allocUnsafe(10); head[0] = 0x81; head[1] = 127; head.writeUInt32BE(0, 2); head.writeUInt32BE(n, 6); }
  return Buffer.concat([head, data]);
}
function sendRaw(c, buf) {
  if (c.dead) return;
  if (c.s.writableLength > 262144) { drop(c, 'slow'); return; }       // клиент не успевает читать
  try { c.s.write(buf); } catch (e) { drop(c, 'write'); }
}
function send(c, msg) { sendRaw(c, frame(JSON.stringify(msg))); }
function broadcast(room, msg, except) { const buf = frame(JSON.stringify(msg)); room.players.forEach(p => { if (p !== except && p.c) sendRaw(p.c, buf); }); }
function humans(room, team) { let n = 0; room.players.forEach(p => { if (!p.bot && (!team || p.team === team)) n++; }); return n; }

function drop(c, why) {
  if (c.dead) return; c.dead = true; conns.delete(c);
  try { c.s.destroy(); } catch (e) { /* уже закрыт */ }
  const p = c.p, room = c.room; c.p = null; c.room = null;
  if (p && room) {
    const now = Date.now();
    if (room.mode === 'bomb') {
      if (p.alive && room.phase === 'live') dropBomb(room, p); else if (room.bomb.carrier === p.id) { room.bomb.carrier = 0; room.bomb.state = 'none'; }
      if (room.ranked && (room.phase === 'freeze' || room.phase === 'live' || room.phase === 'post')) { rate(p, false, avgRating(room, p.grp), avgRating(room, 1 - p.grp), now); saveRatings(); }
    }
    room.players.delete(p.id);
    const left = humans(room);
    log('выход:', p.name, '| комната', room.name, '| осталось', left, why ? '(' + why + ')' : '');
    if (left === 0) { room.players.clear(); rooms.delete(room.name); }      // последний человек вышел: комната закрывается вместе с ботами
    else { broadcast(room, { t: 'leave', id: p.id }); if (room.host === p) room.host = null; fillBots(room, now); roundCheck(room, now); }
  }
}
// сообщение об отказе, затем закрытие
function refuse(c, msg) { send(c, { t: 'err', msg: msg }); sendRaw(c, Buffer.from([0x88, 0])); setTimeout(() => drop(c, msg), 300); }

function onData(c, chunk) {
  c.buf = c.buf && c.buf.length ? Buffer.concat([c.buf, chunk]) : chunk;
  if (c.buf.length > 65536) { drop(c, 'flood'); return; }
  for (;;) {
    const b = c.buf; if (c.dead || !b || b.length < 2) return;
    const fin = b[0] & 0x80, op = b[0] & 0x0f, masked = b[1] & 0x80; let len = b[1] & 0x7f, off = 2;
    if (b[0] & 0x70) { drop(c, 'rsv'); return; }
    if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; } else if (len === 127) { drop(c, 'big'); return; }
    if (!masked || len > MAX_FRAME) { drop(c, 'frame'); return; }
    if (b.length < off + 4 + len) return;
    const data = Buffer.allocUnsafe(len);
    for (let i = 0; i < len; i++) data[i] = b[off + 4 + i] ^ b[off + (i & 3)];
    c.buf = b.subarray(off + 4 + len);
    if (op === 8) { sendRaw(c, Buffer.from([0x88, 0])); drop(c, ''); return; }
    if (op === 9) { if (len < 126) sendRaw(c, Buffer.concat([Buffer.from([0x8a, len]), data])); continue; }
    if (op === 10) continue;
    if (op === 0) { if (!c.frag) { drop(c, 'cont'); return; } c.frag.push(data); c.fragLen += len; }
    else if (op === 1 || op === 2) { if (c.frag) { drop(c, 'frag'); return; } c.frag = [data]; c.fragLen = len; c.fragText = op === 1; }
    else { drop(c, 'op'); return; }
    if (c.fragLen > MAX_FRAME * 2) { drop(c, 'big'); return; }
    if (fin) { const whole = c.frag.length === 1 ? c.frag[0] : Buffer.concat(c.frag), text = c.fragText; c.frag = null; if (text) onText(c, whole.toString('utf8')); }
  }
}

// ---- кто сейчас онлайн: игроки в комнатах и те, у кого игра открыта (она отмечается раз в полминуты) ----
const presence = new Map();
const PID_RE = /^[a-z0-9]{4,16}$/;
function mark(pid, now) { if (typeof pid === 'string' && PID_RE.test(pid) && (presence.has(pid) || presence.size < 5000)) presence.set(pid, now); }
function onlineCount(now) {
  presence.forEach((at, pid) => { if (now - at > 75000) presence.delete(pid); });
  let n = presence.size, playing = 0;
  rooms.forEach(r => r.players.forEach(p => { if (p.bot) return; playing++; if (!p.pid || !presence.has(p.pid)) n++; }));
  return { n: n, playing: playing };
}

// ---- рейтинг: хранится в файле ratings.json рядом с сервером -----------------------------------
const ratings = Object.create(null);
try {
  const raw = JSON.parse(fs.readFileSync(RATE_FILE, 'utf8'));
  if (raw && typeof raw === 'object') for (const k of Object.keys(raw)) {
    const v = raw[k];
    if (UID_RE.test(k) && v && typeof v.r === 'number' && isFinite(v.r)) ratings[k] = { n: cleanName(v.n), r: Math.max(0, Math.min(9999, Math.round(v.r))), g: Math.max(0, v.g | 0), w: Math.max(0, v.w | 0), t: +v.t || 0 };
  }
} catch (e) { /* файла ещё нет: рейтинг начнётся с чистого листа */ }
let rateDirty = false;
function saveRatings() {
  if (!rateDirty) return; rateDirty = false;
  try { fs.writeFileSync(RATE_FILE + '.tmp', JSON.stringify(ratings)); fs.renameSync(RATE_FILE + '.tmp', RATE_FILE); } catch (e) { log('рейтинг не сохранился:', e && e.message); }
}
function rating(uid, name) {
  let r = ratings[uid];
  if (!r) { if (Object.keys(ratings).length >= 20000) return null; r = ratings[uid] = { n: name, r: 1000, g: 0, w: 0, t: Date.now() }; }
  if (name) r.n = name;
  return r;
}
function topList(uid) {
  const all = Object.keys(ratings).filter(k => ratings[k].g > 0).sort((a, b) => ratings[b].r - ratings[a].r || ratings[b].w - ratings[a].w);
  const list = all.slice(0, 50).map(k => ({ n: ratings[k].n, r: ratings[k].r, g: ratings[k].g, w: ratings[k].w, me: k === uid ? 1 : 0 }));
  const mine = uid && ratings[uid] ? ratings[uid] : null;
  return { t: 'top', list: list, place: uid ? all.indexOf(uid) + 1 : 0, r: mine ? mine.r : 1000, g: mine ? mine.g : 0 };
}
// итог рейтингового матча для одного игрока: чем сильнее соперники, тем больше за победу и меньше за поражение
function rate(p, won, ownAvg, oppAvg, now) {
  const r = p.uid ? rating(p.uid, p.name) : null; if (!r) return;
  const expect = 1 / (1 + Math.pow(10, (oppAvg - ownAvg) / 400));
  let d = Math.round(32 * ((won ? 1 : 0) - expect)); if (won && d < 8) d = 8; if (!won && d > -8) d = -8;
  const old = r.r; r.r = Math.max(0, old + d); r.g++; if (won) r.w++; r.t = now; rateDirty = true;
  send(p.c, { t: 'rate', old: old, now: r.r, d: r.r - old, g: r.g });
}
function avgRating(room, grp) { let s = 0, n = 0; room.players.forEach(p => { if (p.grp === grp) { const r = p.uid && ratings[p.uid]; s += r ? r.r : 1000; n++; } }); return n ? s / n : 1000; }

// ---- игра -------------------------------------------------------------------------------------
function pub(p) {
  if (p.bot) return { id: p.id, name: p.name, team: p.team, alive: p.alive, kills: p.kills, deaths: p.deaths, bot: 1 };
  const o = { id: p.id, name: p.name, team: p.team, alive: p.alive, kills: p.kills, deaths: p.deaths }; if (p.admin) o.adm = 1; return o;
}
function newRoom(name, now, mode, map, ranked) {
  const room = { name: name, players: new Map(), nextId: 1, score: { ct: 0, t: 0 }, state: 'live', endsAt: now + MATCH_MS, postUntil: 0, tick: 0,
    mode: mode === 'bomb' ? 'bomb' : 'tdm', map: map === 'lego' && mode !== 'bomb' ? 'lego' : 'town', ranked: !!ranked, size: ranked ? 4 : ROOM_SIZE,
    phase: 'wait', phaseEnd: 0, liveAt: 0, round: 0, wins: [0, 0], side: ['ct', 't'], swapped: false, bomb: { state: 'none', carrier: 0, x: 0, y: 0, z: 0, at: 0 },
    botsOn: false, host: null, botAt: 0, drops: new Map(), nextDrop: 1 };
  rooms.set(name, room); return room;
}
function fighting(room) { return room.state === 'live' && (room.mode !== 'bomb' || room.phase === 'live'); }
function spawn(room, p, now) {
  p.alive = true; p.hp = 100; p.armor = 100; p.helmet = true; p.protectUntil = now + PROTECT_MS; p.respawnAt = 0; p.st = null; p.extra = null;      // (подобранное оружие осталось в прошлой жизни)
  broadcast(room, { t: 'spawn', id: p.id });
}
function endMatch(room, now) {
  if (room.state !== 'live') return;
  room.state = 'post'; room.postUntil = now + POST_MS;
  const s = room.score, win = s.ct === s.t ? null : (s.ct > s.t ? 'ct' : 't');
  broadcast(room, { t: 'end', win: win, s: [s.ct, s.t] });
  log('матч окончен | комната', room.name, '| счёт', s.ct + ':' + s.t);
}
function startMatch(room, now) {
  room.state = 'live'; room.endsAt = now + MATCH_MS; room.score.ct = 0; room.score.t = 0; room.drops.clear();
  room.players.forEach(p => { p.kills = 0; p.deaths = 0; p.alive = false; p.respawnAt = 0; });
  broadcast(room, { t: 'start', left: MATCH_MS, limit: KILL_LIMIT });
  room.players.forEach(p => spawn(room, p, now));
}

// ---- раунды с бомбой --------------------------------------------------------------------------
function count(room, team, aliveOnly) { let n = 0; room.players.forEach(p => { if (p.team === team && (!aliveOnly || p.alive)) n++; }); return n; }
function bombMsg(room, e, id) { const b = room.bomb; broadcast(room, { t: 'bomb', e: e, id: id || 0, x: b.x, y: b.y, z: b.z }); }
function dropBomb(room, p) {
  const b = room.bomb; if (b.state !== 'carried' || b.carrier !== p.id) return;
  let other = null; room.players.forEach(q => { if (!other && q !== p && q.alive && q.team === 't') other = q; });
  if (p.st) { b.state = 'dropped'; b.carrier = 0; b.x = p.st[1]; b.y = p.st[2]; b.z = p.st[3]; bombMsg(room, 'drop'); }
  else if (other) { b.carrier = other.id; bombMsg(room, 'pick', other.id); }       // где упала, неизвестно: бомба переходит напарнику
  else { b.state = 'none'; b.carrier = 0; }
}
function startBomb(room, now) {
  room.wins = [0, 0]; room.round = 0; room.swapped = false; room.state = 'live';
  room.players.forEach(p => { p.kills = 0; p.deaths = 0; });
  log('матч с бомбой начался | комната', room.name, room.ranked ? '| рейтинговый' : '', '| игроков', room.players.size);
  nextRound(room, now);
}
function nextRound(room, now) {
  room.round++;
  if (!room.swapped && room.round === NEED) {                       // середина матча: команды меняются сторонами
    room.swapped = true; room.side.reverse();
    room.players.forEach(p => { p.team = p.team === 'ct' ? 't' : 'ct'; });
  }
  const teams = [], ts = []; room.drops.clear();      // новый раунд: с земли всё убрано, у каждого снова своё оружие
  room.players.forEach(p => { p.alive = true; p.hp = 100; p.armor = 100; p.helmet = true; p.protectUntil = 0; p.respawnAt = 0; p.st = null; p.act = null; p.extra = null; teams.push([p.id, p.team]); if (p.team === 't') ts.push(p); });
  const b = room.bomb; b.state = ts.length ? 'carried' : 'none'; b.carrier = ts.length ? ts[Math.floor(Math.random() * ts.length)].id : 0; b.at = 0;
  room.phase = 'freeze'; room.phaseEnd = now + FREEZE_MS;
  broadcast(room, { t: 'round', n: room.round, wins: room.wins, side: room.side, teams: teams, carrier: b.carrier, freeze: FREEZE_MS });
}
function endRound(room, win, why, now) {
  if (room.phase !== 'live') return;
  room.phase = 'post'; room.phaseEnd = now + ROUND_POST_MS;
  room.wins[room.side.indexOf(win)]++;
  room.players.forEach(p => { p.act = null; });
  broadcast(room, { t: 'rend', win: win, why: why, wins: room.wins });
}
function endBomb(room, now) {
  const g = room.wins[0] >= room.wins[1] ? 0 : 1;
  room.phase = 'over'; room.phaseEnd = now + POST_MS; room.bomb.state = 'none';
  broadcast(room, { t: 'end', win: room.side[g], s: room.wins, g: g });
  log('матч с бомбой окончен | комната', room.name, '| счёт', room.wins[0] + ':' + room.wins[1]);
  if (room.ranked) { const a0 = avgRating(room, 0), a1 = avgRating(room, 1); room.players.forEach(p => rate(p, p.grp === g, p.grp === 0 ? a0 : a1, p.grp === 0 ? a1 : a0, now)); saveRatings(); }
}
function roundCheck(room, now) {
  if (room.mode !== 'bomb' || room.phase !== 'live') return;
  const ct = count(room, 'ct', true), t = count(room, 't', true);
  if (!ct) endRound(room, 't', 'kill', now); else if (!t && room.bomb.state !== 'planted') endRound(room, 'ct', 'kill', now);
}
function near(p, x, y, z, r) { return !!p.st && Math.hypot(p.st[1] - x, p.st[3] - z) <= r && Math.abs(p.st[2] - y) <= 70; }
function tickBomb(room, now) {
  const b = room.bomb, ct = count(room, 'ct'), t = count(room, 't');
  if (room.phase === 'wait') {
    // обычная комната начинает, как только в обеих командах кто-то есть; рейтинговая строго вчетвером, двое на двое
    if (room.ranked ? ct === 2 && t === 2 : ct && t) startBomb(room, now);
    return;
  }
  if (room.phase === 'over') { if (now >= room.phaseEnd) { if (room.ranked ? ct === 2 && t === 2 : ct && t) startBomb(room, now); else room.phase = 'wait'; } return; }
  if (!ct || !t) {                                                   // одна из команд вышла целиком: победа оставшимся
    const g = room.side.indexOf(ct ? 'ct' : 't'); room.wins[g] = Math.max(room.wins[g], NEED); room.wins[1 - g] = Math.min(room.wins[1 - g], NEED - 1);
    endBomb(room, now); return;
  }
  if (room.phase === 'freeze') { if (now >= room.phaseEnd) { room.phase = 'live'; room.liveAt = now; broadcast(room, { t: 'live', left: ROUND_MS }); } return; }
  if (room.phase === 'post') { if (now >= room.phaseEnd) { if (room.wins[0] >= NEED || room.wins[1] >= NEED) endBomb(room, now); else nextRound(room, now); } return; }
  // идёт раунд
  if (b.state === 'dropped') room.players.forEach(p => { if (b.state === 'dropped' && p.alive && p.team === 't' && near(p, b.x, b.y, b.z, 44)) { b.state = 'carried'; b.carrier = p.id; bombMsg(room, 'pick', p.id); } });
  room.players.forEach(p => {
    const a = p.act; if (!a || room.phase !== 'live') return;
    if (!p.alive || !near(p, a.x, a.y, a.z, 40)) { p.act = null; return; }
    if (a.k === 'p' && now - a.at >= PLANT_MS && b.state === 'carried' && b.carrier === p.id) {
      p.act = null; b.state = 'planted'; b.carrier = 0; b.x = p.st[1]; b.y = p.st[2]; b.z = p.st[3]; b.at = now; bombMsg(room, 'plant', p.id);
    } else if (a.k === 'd' && now - a.at >= DEFUSE_MS && b.state === 'planted') {
      p.act = null; b.state = 'none'; bombMsg(room, 'defuse', p.id); endRound(room, 'ct', 'defuse', now);
    }
  });
  if (room.phase !== 'live') return;
  if (b.state === 'planted') {
    if (now - b.at >= FUSE_MS) {
      b.state = 'none'; bombMsg(room, 'boom'); endRound(room, 't', 'boom', now);
      room.players.forEach(p => { if (p.alive && p.st) { const dmg = bombDamage(Math.hypot(p.st[1] - b.x, p.st[2] + 36 - b.y, p.st[3] - b.z)); if (dmg >= 1) damage(room, p, null, dmg, 2, 0.6, 'bomb', now); } });
    }
  } else if (now - room.liveAt >= ROUND_MS) endRound(room, 'ct', 'time', now);
}
function bombAct(room, p, what, now) {
  if (room.mode !== 'bomb') return;
  const b = room.bomb;
  if (what === 'x' || room.phase !== 'live' || !p.alive || !p.st) { p.act = null; return; }
  if (what === 'p') {
    const z = BOMB_ZONE[room.map];
    if (p.team !== 't' || b.state !== 'carried' || b.carrier !== p.id || !z || p.st[1] < z[0] || p.st[1] > z[2] || p.st[3] < z[1] || p.st[3] > z[3]) return;
    p.act = { k: 'p', at: now, x: p.st[1], y: p.st[2], z: p.st[3] };
  } else if (what === 'd') {
    if (p.team !== 'ct' || b.state !== 'planted' || !near(p, b.x, b.y, b.z, 70)) return;
    p.act = { k: 'd', at: now, x: p.st[1], y: p.st[2], z: p.st[3] };
  }
}

// ---- оружие на земле ---------------------------------------------------------------------------
// что выпало: номер (по нему его просят), оружие и скин, как их назвала игра хозяина, и где он стоял
function addDrop(room, widx, skin, st, now) {
  if (!st || !(widx >= 0 && widx < W_IDS.length)) return null;          // нож в руках (или о бойце ещё ничего не известно): ничего не падает
  const d = { id: room.nextDrop++, w: widx, skin: skin | 0, x: st[1], y: st[2], z: st[3], at: now };
  room.drops.set(d.id, d);
  if (room.drops.size > DROP_MAX) room.drops.delete(room.drops.keys().next().value);      // самое старое убирается
  return d;
}
function dropMsg(d) { return [d.id, d.w, d.skin, d.x, d.y, d.z]; }
function kill(room, victim, attacker, wid, head, now) {
  const bombRoom = room.mode === 'bomb';
  victim.alive = false; victim.hp = 0; victim.deaths++; victim.respawnAt = bombRoom ? 0 : now + RESPAWN_MS; victim.act = null;
  if (attacker && attacker !== victim) { attacker.kills++; if (attacker.team !== victim.team && !bombRoom) room.score[attacker.team]++; }
  const fell = victim.st ? addDrop(room, victim.st[7] | 0, victim.st[9] | 0, victim.st, now) : null;
  const msg = { t: 'kill', v: victim.id, k: attacker && attacker !== victim ? attacker.id : -1, w: wid, h: head ? 1 : 0, s: bombRoom ? null : [room.score.ct, room.score.t] };
  if (fell) msg.d = dropMsg(fell);
  broadcast(room, msg);
  if (bombRoom) { dropBomb(room, victim); victim.st = null; roundCheck(room, now); return; }
  victim.st = null;
  if (room.score.ct >= KILL_LIMIT || room.score.t >= KILL_LIMIT) endMatch(room, now);
}
function damage(room, victim, attacker, dmg, group, ap, wid, now) {
  const armored = victim.armor > 0 && (group === 1 ? victim.helmet : group !== 4);
  if (attacker && attacker.bot) dmg *= BOT_DMG;
  if (armored && (attacker || wid === 'bomb')) { const through = dmg * ap; victim.armor = Math.max(0, victim.armor - (dmg - through) * 0.5); dmg = through; }
  dmg = Math.max(1, Math.round(dmg));
  victim.hp -= dmg;
  if (victim.bot) { if (room.host) send(room.host.c, { t: 'hurt', id: victim.id, hp: Math.max(0, victim.hp), ar: Math.round(victim.armor), k: attacker ? attacker.id : -1, g: group }); }
  else send(victim.c, { t: 'hurt', hp: Math.max(0, victim.hp), ar: Math.round(victim.armor), k: attacker ? attacker.id : -1, g: group });
  if (victim.hp <= 0) kill(room, victim, attacker, wid, group === 1 && !!attacker, now);
}
// стрелять можно не чаще, чем позволяет ствол (с небольшим запасом на задержки сети)
function allowHit(p, wid, w, now) {
  let b = p.budget[wid]; const cap = w[4] * 2 + 1;
  if (!b) b = p.budget[wid] = { n: cap, at: now };
  b.n = Math.min(cap, b.n + (now - b.at) * (w[4] / w[3]) * 1.25); b.at = now;
  if (b.n < 1) return false; b.n -= 1; return true;
}
function target(room, p, id, now) {
  if (!fighting(room) || !p.alive) return null;
  const v = room.players.get(id);
  if (!v || v === p || !v.alive || v.team === p.team || now < v.protectUntil) return null;
  return v;
}

// ---- боты командного боя ----------------------------------------------------------------------
// Бот это участник комнаты без своего соединения: где он и в кого попал, сообщает игра хозяина,
// а здоровье, счёт и возрождение ведёт сервер, как у людей.
function ableHost(p, now) { return !p.bot && p.cv >= BOT_BUILD && now - p.seen < HOST_LAG_MS; }
function botCount(room, team) { let n = 0; room.players.forEach(p => { if (p.bot && (!team || p.team === team)) n++; }); return n; }
function addBot(room, team, now) {
  const taken = {}; room.players.forEach(p => { taken[p.name] = true; });
  const free = BOT_NAMES.filter(n => !taken[n]), name = free.length ? free[Math.floor(Math.random() * free.length)] : 'Бот ' + room.nextId;
  const b = { id: room.nextId++, c: null, bot: true, name: name, team: team, grp: room.side.indexOf(team), uid: '', pid: '', party: '', cv: 0, alive: false, hp: 100, armor: 100, helmet: true,
    kills: 0, deaths: 0, st: null, act: null, respawnAt: 0, protectUntil: 0, seen: now, budget: {}, knifeAt: 0, chatAt: 0 };
  room.players.set(b.id, b);
  broadcast(room, { t: 'join', p: pub(b) });
  if (room.state === 'live') spawn(room, b, now);
}
function removeBot(room, team) {
  // уходит тот, кого меньше жалко: сначала убитый, потом с меньшим счётом
  let pick = null; room.players.forEach(p => { if (p.bot && p.team === team && (!pick || (pick.alive && !p.alive) || (pick.alive === p.alive && p.kills < pick.kills))) pick = p; });
  if (!pick) return false;
  room.players.delete(pick.id); broadcast(room, { t: 'leave', id: pick.id }); return true;
}
// кто ведёт ботов: об этом узнают все, а новому хозяину заодно сообщается здоровье каждого бота
function setHost(room, p) {
  room.host = p; const list = [];
  room.players.forEach(q => { if (q.bot) list.push([q.id, Math.max(0, q.hp), Math.round(q.armor), q.alive ? 1 : 0]); });
  broadcast(room, { t: 'host', id: p ? p.id : 0, bots: list });
  if (p) log('ботов ведёт:', p.name, '| комната', room.name);
}
// привести ботов комнаты в порядок: кто их ведёт и сколько их должно быть в каждой команде
function botRoom(room) { return BOT_TEAM > 0 && room.mode === 'tdm' && !room.ranked && (room.auto || room.name.indexOf('bs-') === 0); }      // общие комнаты боя; в своей комнате (имя выбрали сами игроки) ботов нет
function fillBots(room, now) {
  if (!botRoom(room)) return;
  let host = room.host && room.players.get(room.host.id) === room.host ? room.host : null, able = null;
  room.players.forEach(p => { if (!able && p !== host && ableHost(p, now)) able = p; });
  if (host && !ableHost(host, now) && able) host = null;            // хозяин завис, а подхватить есть кому
  if (!host) host = able;
  if (humans(room) >= 2) room.botsOn = true;                        // двое живых: дальше команды добираются ботами
  const on = BOT_TEAM > 0 && room.botsOn && !!host;
  if (host !== room.host) setHost(room, host);
  for (const team of ['ct', 't']) {
    const want = on ? Math.max(0, BOT_TEAM - humans(room, team)) : 0; let have = botCount(room, team);
    while (have > want && removeBot(room, team)) have--;
    while (have < want) { addBot(room, team, now); have++; }
  }
}
// положение бойца из сообщения: x y z, поворот, наклон, присед, оружие, флаги, скин
function stateOf(id, m) {
  return [id, Math.round(num(m[1], -1e5, 1e5, 0) * 10) / 10, Math.round(num(m[2], -1e5, 1e5, 0) * 10) / 10, Math.round(num(m[3], -1e5, 1e5, 0) * 10) / 10,
    Math.round(num(m[4], -1e4, 1e4, 0) * 1000) / 1000, Math.round(num(m[5], -1.6, 1.6, 0) * 1000) / 1000, Math.round(num(m[6], 0, 1, 0) * 100) / 100, num(m[7], 0, 99, 0) | 0, num(m[8], 0, 255, 0) | 0,
    num(m[9], 0, 999, 0) | 0];
}

// ---- пати -------------------------------------------------------------------------------------
// У каждого игрока свой код. Кто ввёл у себя чужой код, идёт за его хозяином; общий код пати
// сервер находит, пройдя по этим ссылкам (двое ввели коды друг друга: берётся меньший из двух).
const PARTY_RE = /^[A-Z0-9]{4,8}$/;
const partyLink = new Map();      // свой код -> { to: введённый чужой код или '', at: когда сообщил }
const partyMenu = new Map();      // код пати -> Map(отметка игрока -> { n: имя, at: когда отмечался в меню })
const partyWhere = new Map();     // отметка игрока -> код пати, в чьём меню он числится (перешёл в другое пати: из старого убирается сразу)
function partyOf(own, to, now) {
  if (typeof own !== 'string' || !PARTY_RE.test(own)) return '';
  to = typeof to === 'string' && PARTY_RE.test(to) && to !== own ? to : '';
  if (partyLink.has(own) || partyLink.size < 5000) partyLink.set(own, { to: to, at: now });
  let cur = own; const seen = [own];
  for (let i = 0; i < 6; i++) {
    const l = partyLink.get(cur); if (!l || !l.to || now - l.at > 600000) break;
    if (seen.indexOf(l.to) >= 0) { let m = seen[0]; for (const s of seen) if (s < m) m = s; return m; }
    cur = l.to; seen.push(cur);
  }
  return cur;
}
function joinable(r) { return humans(r) < r.size && !(r.ranked && r.phase !== 'wait'); }
// друг из того же пати, к которому можно зайти: выбирается комната, где людей больше
function partyMate(code, uid) {
  if (!code) return null; let best = null;
  rooms.forEach(r => { if (!joinable(r)) return; r.players.forEach(p => { if (!p.bot && p.party === code && (!uid || p.uid !== uid) && (!best || humans(r) > humans(best.room))) best = { room: r, p: p }; }); });
  return best;
}
// кто ещё в этом пати: в бою (s: 1, можно ли к нему зайти) и в меню (s: 0); заодно отмечается сам спросивший
function partyList(code, pid, name, now) {
  let m = partyMenu.get(code); if (!m && partyMenu.size < 3000) partyMenu.set(code, m = new Map());
  if (m && typeof pid === 'string' && PID_RE.test(pid) && (m.has(pid) || m.size < 12)) {
    const was = partyWhere.get(pid); if (was && was !== code) { const old = partyMenu.get(was); if (old) old.delete(pid); }
    if (partyWhere.has(pid) || partyWhere.size < 20000) partyWhere.set(pid, code);
    m.set(pid, { n: cleanName(name), at: now });
  }
  const out = [], inRoom = {};
  rooms.forEach(r => r.players.forEach(p => { if (!p.bot && p.party === code && p.pid !== pid) { inRoom[p.pid] = 1; out.push({ n: p.name, s: 1, m: r.ranked ? 'ranked' : r.mode, o: joinable(r) ? 1 : 0 }); } }));
  if (m) m.forEach((v, k) => { if (now - v.at > 45000) m.delete(k); else if (k !== pid && !inRoom[k]) out.push({ n: v.n, s: 0 }); });
  return out.slice(0, 8);
}
setInterval(() => {
  const now = Date.now();
  rooms.forEach(r => r.players.forEach(p => { const l = p.own ? partyLink.get(p.own) : null; if (l) l.at = now; }));      // кто в бою, тот в пати остаётся
  partyLink.forEach((l, k) => { if (now - l.at > 900000) partyLink.delete(k); });
  partyMenu.forEach((m, k) => { m.forEach((v, q) => { if (now - v.at > 45000) { m.delete(q); if (partyWhere.get(q) === k) partyWhere.delete(q); } }); if (!m.size) partyMenu.delete(k); });
}, 60000);

// вход без выбора комнаты: самая заполненная общая комната этого режима, где ещё есть место; если такой нет, открывается новая
function autoRoom(now, mode) {
  let best = null; const ranked = mode === 'ranked', kind = ranked ? 'bomb' : mode;
  rooms.forEach(r => {
    const n = humans(r);
    if (!r.auto || r.mode !== kind || r.ranked !== ranked || n >= r.size) return;
    if (ranked && r.phase !== 'wait') return;                        // в начатый рейтинговый матч не подсаживают
    if (!best || n > humans(best)) best = r;
  });
  if (best) return best;
  if (rooms.size >= MAX_ROOMS) return null;
  const prefix = ranked ? 'rank-' : (kind === 'bomb' ? 'bomb-' : 'arena-');
  for (let i = 1; ; i++) if (!rooms.has(prefix + i)) { const r = newRoom(prefix + i, now, kind, 'town', ranked); r.auto = true; return r; }
}
// «Сейчас играют» в меню игры: общие бои, где есть люди и есть место (свои комнаты и рейтинговые матчи сюда не попадают)
function liveList() {
  const list = [];
  rooms.forEach(r => {
    const n = humans(r); if (!n || r.ranked || !joinable(r) || !(r.auto || r.name.indexOf('bs-') === 0)) return;
    const names = []; r.players.forEach(p => { if (!p.bot && names.length < 3) names.push(p.name); });
    list.push({ room: r.name, n: n, bots: botCount(r), max: r.size, mode: r.mode, map: r.map, names: names });
  });
  list.sort((a, b) => b.n - a.n);
  return list.slice(0, 3);
}
// комнаты, где сейчас играют: сначала самые людные
function roomList(now) {
  const list = [];
  rooms.forEach(r => {
    const names = []; let bots = 0; r.players.forEach(p => { if (p.bot) bots++; else names.push(p.name); });
    const bombRoom = r.mode === 'bomb';
    list.push({ room: r.name, n: names.length, bots: bots, max: r.size, s: bombRoom ? r.wins : [r.score.ct, r.score.t], state: r.state, left: Math.max(0, r.endsAt - now), names: names,
      mode: r.mode, map: r.map, ranked: r.ranked ? 1 : 0, open: r.ranked && r.phase !== 'wait' ? 0 : 1 });
  });
  list.sort((a, b) => b.n - a.n);
  return list.slice(0, 12);
}
function onJoin(c, m, now) {
  if (m.v !== VERSION || !((m.cv | 0) >= MIN_BUILD)) { refuse(c, 'version'); return; }      // у старой игры другая карта: ей нужно обновление
  const uid = typeof m.uid === 'string' && UID_RE.test(m.uid) ? m.uid : '';
  const mode = m.mode === 'ranked' ? 'ranked' : (m.mode === 'bomb' ? 'bomb' : 'tdm');
  const wanted = String(m.room == null ? '' : m.room).trim(); let room;
  const party = partyOf(m.own, m.party, now), mate = partyMate(party, uid);
  if (mate && (uid || !mate.room.ranked)) room = mate.room;          // друг из пати уже в комнате: туда же, какую бы комнату ни просили
  else if (mode === 'ranked' || !wanted || wanted === 'auto') {
    if (mode === 'ranked' && !uid) { refuse(c, 'version'); return; }
    room = autoRoom(now, mode); if (!room) { refuse(c, 'rooms'); return; }
  } else {
    const roomName = cleanRoom(wanted); room = rooms.get(roomName);
    if (!room) { if (rooms.size >= MAX_ROOMS) { refuse(c, 'rooms'); return; } room = newRoom(roomName, now, mode, m.map, false); }
    if (!joinable(room)) { refuse(c, 'full'); return; }
  }
  let ct = 0, t = 0; const taken = {};
  room.players.forEach(p => { taken[p.name] = true; if (p.bot) return; if (p.team === 'ct') ct++; else t++; });      // команды равняются по людям: боты подстроятся
  const side = room.ranked ? 2 : Math.ceil(room.size / 2);
  const team = mate && mate.room === room && humans(room, mate.p.team) < side ? mate.p.team : (ct === t ? (m.team === 't' ? 't' : 'ct') : (ct < t ? 'ct' : 't'));
  let name = cleanName(m.name); for (let i = 2; taken[name]; i++) name = cleanName(m.name).slice(0, 11) + ' ' + i;
  const p = { id: room.nextId++, c: c, name: name, team: team, grp: room.side.indexOf(team), uid: uid, pid: typeof m.pid === 'string' && PID_RE.test(m.pid) ? m.pid : '', party: party, own: party && typeof m.own === 'string' ? m.own : '', cv: m.cv | 0, admin: m.adm === ADMIN_KEY, extra: null, alive: false, hp: 100, armor: 100, helmet: true, kills: 0, deaths: 0, st: null, act: null, respawnAt: 0, protectUntil: 0, seen: now, budget: {}, knifeAt: 0, chatAt: 0 };
  c.p = p; c.room = room; room.players.set(p.id, p);
  if (uid && room.ranked) rating(uid, name);
  const list = []; room.players.forEach(q => list.push(pub(q)));
  const bombRoom = room.mode === 'bomb', b = room.bomb, drops = [];
  room.drops.forEach(d => { if (now - d.at < dropLife(room) - 2000) drops.push(dropMsg(d)); });
  const pleft = !bombRoom ? 0 : (room.phase === 'live' ? (b.state === 'planted' ? FUSE_MS - (now - b.at) : ROUND_MS - (now - room.liveAt)) : Math.max(0, room.phaseEnd - now));
  send(c, { t: 'welcome', v: VERSION, id: p.id, name: p.name, room: room.name, team: team, limit: KILL_LIMIT, size: room.size, state: room.state, left: Math.max(0, room.endsAt - now), now: now, s: [room.score.ct, room.score.t], players: list,
    mode: room.mode, map: room.map, ranked: room.ranked ? 1 : 0, need: NEED, wins: room.wins, side: room.side, round: room.round, phase: room.phase, pleft: Math.max(0, pleft),
    bomb: bombRoom ? { state: b.state, carrier: b.carrier, x: b.x, y: b.y, z: b.z } : null, rating: uid && ratings[uid] ? ratings[uid].r : 1000,
    host: room.host ? room.host.id : 0, bots: botRoom(room) ? BOT_TEAM : 0, mate: mate && mate.room === room ? mate.p.id : 0, mapv: MAP_VER, adm: p.admin ? 1 : 0, drops: drops });
  broadcast(room, { t: 'join', p: pub(p) }, p);
  if (party) room.players.forEach(q => { if (q !== p && q.c && q.party === party) send(q.c, { t: 'mate', id: p.id }); });      // друзьям из пати: свой зашёл
  log('вход:', p.name, '| комната', room.name, '| игроков', humans(room), mate && mate.room === room ? '| к другу из пати' : '');
  if (!bombRoom && room.state === 'live') spawn(room, p, now);       // в комнате с бомбой новичок выходит со следующего раунда
  fillBots(room, now);
}

function onText(c, text) {
  const now = Date.now();
  if (now - c.rlAt > 1000) { c.rlAt = now; c.rl = 0; }
  if (++c.rl > 720) { drop(c, 'flood'); return; }      // (игра, которая ведёт девять ботов, сообщает и их выстрелы с попаданиями)
  let m; try { m = JSON.parse(text); } catch (e) { return; }
  const p = c.p, room = c.room;
  if (!Array.isArray(m)) {
    if (m && m.t === 'join' && !p) onJoin(c, m, now);
    else if (m && m.t === 'rooms') { c.at = now; send(c, { t: 'rooms', list: roomList(now) }); }      // кто сейчас играет: для списка комнат в игре
    else if (m && m.t === 'on') {      // счётчик онлайна для главного меню; заодно игра узнаёт свой рейтинг
      c.at = now; mark(m.p, now); const o = onlineCount(now), mine = typeof m.uid === 'string' && UID_RE.test(m.uid) ? ratings[m.uid] : null;
      const party = partyOf(m.own, m.party, now);
      send(c, { t: 'on', n: o.n, playing: o.playing, rooms: rooms.size, r: mine ? mine.r : 1000, g: mine ? mine.g : 0, pc: party, pm: party ? partyList(party, m.p, m.name, now) : [], live: liveList() });
    }
    else if (m && m.t === 'top') { c.at = now; if (now - (c.topAt || 0) > 900) { c.topAt = now; send(c, topList(typeof m.uid === 'string' && UID_RE.test(m.uid) ? m.uid : '')); } }
    return;
  }
  if (!p || !room) return;
  p.seen = now;
  switch (m[0]) {
    case 's':                                             // моё положение: x y z, поворот, наклон, присед, оружие, флаги
      if (!p.alive) return;
      p.st = stateOf(p.id, m);                             // (последнее число: какой скин на оружии, чтобы его видели все)
      if (!p.admin) p.st[8] &= 7;                          // перчатки админа (старшие биты флагов) есть только у админа
      return;
    // ---- хозяин ботов сообщает за них: положение, выстрел, попадание, удар ножом, падение ----
    case 'S':
      if (room.host !== p || !Array.isArray(m[1])) return;
      for (const e of m[1].slice(0, 16)) { const b = Array.isArray(e) ? room.players.get(e[0]) : null; if (b && b.bot && b.alive) { b.st = stateOf(b.id, e); b.st[8] &= 7; } }
      return;
    case 'F': {
      const b = room.players.get(m[1]); if (room.host !== p || !b || !b.bot || !b.alive || !fighting(room)) return;
      broadcast(room, ['f', b.id, num(m[2], 0, 99, 0) | 0, Math.round(num(m[3], -1e5, 1e5, 0)), Math.round(num(m[4], -1e5, 1e5, 0)), Math.round(num(m[5], -1e5, 1e5, 0)), m[6] ? 1 : 0], p);
      return;
    }
    case 'H': {
      const b = room.players.get(m[1]); if (room.host !== p || !b || !b.bot) return;
      const wid = typeof m[3] === 'string' ? m[3] : '', w = Object.prototype.hasOwnProperty.call(WEAPONS, wid) ? WEAPONS[wid] : null, v = target(room, b, m[2], now);
      const group = num(m[4], 1, 4, 2) | 0;
      if (!w || !v || (SIDE[wid] && SIDE[wid] !== b.team) || !allowHit(b, wid, w, now)) return;
      damage(room, v, b, w[0] * Math.pow(w[1], num(m[5], 0, 8192, 0) / 500) * HIT_MULT[group], group, w[2], wid, now);
      return;
    }
    case 'K': {
      const b = room.players.get(m[1]); if (room.host !== p || !b || !b.bot) return;
      const v = target(room, b, m[2], now), kind = num(m[3], 0, 3, 0) | 0;
      if (!v || now - b.knifeAt < 350) return;
      if (b.st && v.st && Math.hypot(b.st[1] - v.st[1], b.st[2] - v.st[2], b.st[3] - v.st[3]) > 260) return;
      b.knifeAt = now;
      damage(room, v, b, KNIFE_DMG[kind], 2, KNIFE_AP, typeof m[4] === 'string' ? m[4].slice(0, 16) : 'knife_ct', now);
      return;
    }
    case 'D': {
      const b = room.players.get(m[1]); if (room.host !== p || !b || !b.bot || !b.alive || !fighting(room)) return;
      damage(room, b, null, num(m[2], 1, 1000, 1), 4, 1, 'fall', now);
      return;
    }
    case 'g':                                             // одиночка просит начать бой с ботами, не дожидаясь второго игрока
      if (botRoom(room) && p.cv >= BOT_BUILD && !room.botsOn) { room.botsOn = true; fillBots(room, now); log('бой с ботами начат | комната', room.name, '| просил', p.name); }
      return;
    case 'c': {                                           // чат: 0 всем в комнате, 1 только своей команде
      const text = cleanChat(m[2]);
      if (!text || now - p.chatAt < 500) return;
      p.chatAt = now;
      const scope = m[1] ? 1 : 0, buf = frame(JSON.stringify(['c', p.id, scope, text]));
      room.players.forEach(q => { if (q.c && (!scope || q.team === p.team)) sendRaw(q.c, buf); });
      return;
    }
    case 'f':                                             // выстрел или взмах ножом: показать остальным
      if (!p.alive || !fighting(room)) return;
      broadcast(room, ['f', p.id, num(m[1], 0, 99, 0) | 0, Math.round(num(m[2], -1e5, 1e5, 0)), Math.round(num(m[3], -1e5, 1e5, 0)), Math.round(num(m[4], -1e5, 1e5, 0)), m[5] ? 1 : 0], p);
      return;
    case 'h': {                                           // попадание пулей: в кого, из чего, куда, с какого расстояния
      const wid = typeof m[2] === 'string' ? m[2] : '', w = Object.prototype.hasOwnProperty.call(WEAPONS, wid) ? WEAPONS[wid] : null, v = target(room, p, m[1], now);
      const group = num(m[3], 1, 4, 2) | 0;
      if (!w || !v || (SIDE[wid] && SIDE[wid] !== p.team && !(p.extra && p.extra[wid])) || !allowHit(p, wid, w, now)) return;      // чужой стороны ствол урона не наносит, если он не подобран с земли
      damage(room, v, p, w[0] * Math.pow(w[1], num(m[4], 0, 8192, 0) / 500) * HIT_MULT[group], group, w[2], wid, now);
      return;
    }
    case 'k': {                                           // удар ножом
      const v = target(room, p, m[1], now), kind = num(m[2], 0, 3, 0) | 0;
      if (!v || now - p.knifeAt < 350) return;
      if (p.st && v.st && Math.hypot(p.st[1] - v.st[1], p.st[2] - v.st[2], p.st[3] - v.st[3]) > 260) return;      // слишком далеко для ножа
      p.knifeAt = now;
      damage(room, v, p, KNIFE_DMG[kind], 2, KNIFE_AP, typeof m[3] === 'string' ? m[3].slice(0, 16) : 'knife_ct', now);
      return;
    }
    case 'd':                                             // урон самому себе: падение с высоты или за край карты
      if (!p.alive || !fighting(room)) return;
      damage(room, p, null, num(m[1], 1, 1000, 1), 4, 1, 'fall', now);
      return;
    case 'u': {                                           // подобрать оружие с земли: его номер; что игрок бросает взамен (место в списке оружия или -1) и скин на нём
      const id = num(m[1], 0, 1e9, 0) | 0, d = room.drops.get(id);
      if (!d || now - d.at > dropLife(room)) { if (d) room.drops.delete(id); send(c, { t: 'pick', d: id, id: 0 }); return; }      // его уже нет: игра спросившего убирает его у себя
      if (!p.alive || !p.st || Math.hypot(p.st[1] - d.x, p.st[3] - d.z) > 230 || Math.abs(p.st[2] - d.y) > 130) return;      // далеко: не дотянуться
      room.drops.delete(id);
      const wid = W_IDS[d.w], ow = num(m[2], -1, 99, -1) | 0, oid = ow >= 0 ? W_IDS[ow] : null; let fell = null;
      // взамен падает то, что было у него в этом месте: только оружие, которое он и вправду мог носить (своей стороны или тоже подобранное)
      if (oid && (!SIDE[oid] || SIDE[oid] === p.team || (p.extra && p.extra[oid]))) { if (p.extra && oid !== wid) delete p.extra[oid]; fell = addDrop(room, ow, num(m[3], 0, 999, 0) | 0, p.st, now); }
      if (!p.extra) p.extra = {};
      p.extra[wid] = 1;                                    // с этой минуты и до смерти ствол его: урон из него засчитывается, чьей бы стороны он ни был
      broadcast(room, { t: 'pick', d: id, id: p.id, n: fell ? dropMsg(fell) : null });
      return;
    }
    case 't': {                                           // выбросить оружие из рук (например, для друга): какое (место в списке) и скин на нём
      const ow = num(m[1], -1, 99, -1) | 0, oid = ow >= 0 ? W_IDS[ow] : null;
      if (!p.alive || !p.st || !oid || now - (p.throwAt || 0) < 400) return;
      if (SIDE[oid] && SIDE[oid] !== p.team && !(p.extra && p.extra[oid])) return;      // только то, что он и вправду мог носить
      p.throwAt = now; if (p.extra) delete p.extra[oid];
      const fell = addDrop(room, ow, num(m[2], 0, 999, 0) | 0, p.st, now);
      if (fell) broadcast(room, { t: 'pick', d: 0, id: p.id, n: dropMsg(fell) });      // (то же сообщение, что при подборе: никто ничего не взял, но на земле новое оружие)
      return;
    }
    case 'b': bombAct(room, p, m[1] === 'p' ? 'p' : (m[1] === 'd' ? 'd' : 'x'), now); return;      // бомба: начать закладку, начать разминирование, бросить
    case 'p': send(c, ['p', num(m[1], 0, 1e15, 0)]); return;      // проверка задержки
  }
}

setInterval(() => {
  const now = Date.now();
  conns.forEach(c => { if (!c.p && now - c.at > 10000) drop(c, 'нет входа'); });
  rooms.forEach(room => {
    room.tick++;
    room.players.forEach(p => { if (!p.bot && now - p.seen > IDLE_MS) drop(p.c, 'тишина'); });
    if (!room.players.size) return;
    if (now - room.botAt >= 1000) { room.botAt = now; fillBots(room, now); room.drops.forEach((d, id) => { if (now - d.at > dropLife(room)) room.drops.delete(id); }); }      // раз в секунду: не завис ли хозяин ботов, хватает ли их; не залежалось ли оружие на земле
    if (room.mode === 'bomb') tickBomb(room, now);
    else if (room.state === 'live') {
      room.players.forEach(p => { if (!p.alive && p.respawnAt && now >= p.respawnAt) spawn(room, p, now); });
      if (now >= room.endsAt) endMatch(room, now);
    } else if (now >= room.postUntil) startMatch(room, now);
    const list = []; room.players.forEach(p => { if (p.alive && p.st) list.push(p.st); });
    if (list.length || room.tick % 10 === 0) broadcast(room, ['S', now, list]);
  });
}, TICK_MS);
setInterval(saveRatings, 20000);

// ---- сеть -------------------------------------------------------------------------------------
const server = http.createServer((req, res) => {
  let players = 0; rooms.forEach(r => { players += humans(r); });
  const now = Date.now(), url = String(req.url || '/').split('?'), q = /(?:^|&)p=([a-z0-9]{4,16})(?:&|$)/.exec(url[1] || '');
  if (q) mark(q[1], now);
  const on = onlineCount(now);
  if (url[0] === '/status') {
    const list = []; rooms.forEach(r => list.push({ room: r.name, mode: r.mode, map: r.map, ranked: r.ranked, players: humans(r), bots: botCount(r), score: r.mode === 'bomb' ? r.wins : [r.score.ct, r.score.t] }));
    res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8', 'Access-Control-Allow-Origin': '*', 'Cache-Control': 'no-store' });
    res.end(JSON.stringify({ ok: true, name: 'brick-strike', version: VERSION, online: on.n, players: players, rooms: list, uptime: Math.round(process.uptime()) }));
    return;
  }
  res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end('Brick Strike: сервер работает.\nСейчас онлайн: ' + on.n + ' (в матчах ' + players + '), комнат: ' + rooms.size + '\nВ игре укажи адрес этого сервера и порт ' + PORT + '.\n');
});
server.on('upgrade', (req, socket) => {
  const key = req.headers['sec-websocket-key'];
  if (!key || String(req.headers.upgrade || '').toLowerCase() !== 'websocket' || conns.size >= MAX_CONN) { socket.destroy(); return; }
  const accept = crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  socket.setNoDelay(true); socket.setKeepAlive(true, 30000);
  const c = { s: socket, buf: null, frag: null, fragLen: 0, fragText: true, p: null, room: null, dead: false, at: Date.now(), rl: 0, rlAt: Date.now() };
  conns.add(c);
  socket.on('data', chunk => { try { onData(c, chunk); } catch (e) { log('ошибка в сообщении:', e && e.message); drop(c, 'error'); } });
  socket.on('close', () => drop(c, ''));
  socket.on('error', () => drop(c, ''));
});
server.on('clientError', (err, socket) => { try { socket.destroy(); } catch (e) { /* закрыт */ } });
process.on('uncaughtException', e => log('необработанная ошибка:', e && e.stack || e));
process.on('SIGTERM', () => { saveRatings(); process.exit(0); });
process.on('SIGINT', () => { saveRatings(); process.exit(0); });
server.listen(PORT, '0.0.0.0', () => log('Brick Strike 2.7: сервер слушает порт ' + PORT + ' | командный бой до ' + KILL_LIMIT + ' убийств или ' + MATCH_MS / 60000 + ' мин' + (BOT_TEAM ? ', боты добирают команды до ' + BOT_TEAM : ', без ботов') + ' | бомба до ' + NEED + ' побед, рейтинг строго 2 на 2 и только между игроками | оружие по сторонам | пати по коду | в комнате до ' + ROOM_SIZE + ' игроков | рейтинг: ' + RATE_FILE));
