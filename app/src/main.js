// UI shell: modes, input, loop, DOM. Everything it shows is computed by the pure modules.
import presets from '../data/presets.json';
import { PLACES, WINDOW } from './presets.js';
import { rasterize, torus, girth } from './raster.js';
import { init, halfStep, breakDown, fromGrid, isStalled, greenAxis, CLASSIC, TRAIN, DEFAULTS } from './sim.js';
import { certificate, onStreet, isGridlock } from './analysis.js';
import { levelSpec, newLevel, tick, contact, movePlayer, HZ, RULESETS, GRIDLOCK } from './game.js';
import { drawMaze, drawFrame, drawDiagram, cellPx, COLORS } from './render.js';
import { fetchRoads, locate, driveSide } from './fetch.js';
import { makeRng } from './rng.js';
import * as audio from './audio.js';

const $ = (id) => document.getElementById(id);
const canvas = $('screen');
const g = canvas.getContext('2d');
const [CW, CH] = [WINDOW.cols * 4, WINDOW.rows * 4];
canvas.width = CW; canvas.height = CH;

// ---------- places ----------
const places = new Map(presets.places.map((p) => [p.id, { ...p, drive: PLACES.find((q) => q.id === p.id).drive }]));
const nets = new Map();
const netFor = (id) => {
  if (!nets.has(id)) {
    const p = places.get(id);
    const net = rasterize(p.roads, { ...WINDOW, drive: p.drive });
    nets.set(id, { net, girth: girth(net), px: 4, maze: drawMaze(net, 4) });
  }
  return nets.get(id);
};

// ---------- app state (the only mutable object) ----------
const app = {
  mode: 'title', placeId: 'midtown', paused: false, fx: [], acc: 0, pacAcc: 0, last: performance.now(),
  hist: [], sweep: [], sweeping: null, msg: '', high: 0,
  opts: { ...DEFAULTS, green: 6, box: true, crossTurns: false, slow: 0.1 }, rho: 0.3, speed: HZ,
  lab: { W: 48, H: 32, p: 0.32, rule: CLASSIC, seed: 1, status: '' },
};
try { app.high = +localStorage.getItem('gridlock-city-high') || 0; } catch { /* storage blocked */ }

const view = () => app.cur;

const loadSandbox = (seed = 1) => {
  const { net, girth: gr, px, maze } = netFor(app.placeId);
  app.cur = { net, girth: gr, px, maze, sim: init(net, Math.round(net.roadCells * app.rho), seed, app.opts), opts: app.opts };
  app.hist = []; app.sweep = [];
};

const loadLab = () => {
  const { W, H, p, rule, seed } = app.lab;
  const net = torus(W, H);
  const r = makeRng(seed);
  const grid = Array.from({ length: H }, () => Array.from({ length: W }, () => {
    const u = r.float();
    return u < p / 2 ? 1 : u < p ? 2 : 0;
  }));
  const px = cellPx(net, CW, CH);
  app.cur = { net, girth: Math.min(W, H), px, maze: drawMaze(net, px), sim: fromGrid(net, grid), opts: { ...DEFAULTS, rule }, lab: true };
  app.hist = [];
};

const loadLevel = (n, prev) => {
  const spec = levelSpec(n);
  app.placeId = spec.place;
  const { net, girth: gr, px, maze } = netFor(spec.place);
  const { sim, game } = newLevel(net, spec, prev, 1000 + n);
  app.cur = { net, girth: gr, px, maze, sim, opts: spec.rules };
  app.game = game; app.hist = []; app.fx = [];
  banner(`LEVEL ${n + 1}`, `${places.get(spec.place).name}\n${spec.rules.name} · QUOTA ${game.quota} TRIPS`, 2200);
};

// ---------- banners & effects ----------
let bannerUntil = 0;
const banner = (title, sub = '', ms = 0) => {
  $('banner-title').textContent = title;
  $('banner-sub').textContent = sub;
  $('banner').hidden = false;
  bannerUntil = ms ? performance.now() + ms : Infinity;
};
const hideBanner = () => { $('banner').hidden = true; bannerUntil = 0; };

const FX = {
  incident: ['TOWED +300', COLORS.hazard], core: ['LOOP BROKEN +500', COLORS.white],
  captured: ['+100', COLORS.cool], hit: ['CRASH!', COLORS.ghosts[0]], breakdown: ['BREAKDOWN', COLORS.hazard],
};
const effects = (events) => events.forEach((e) => {
  const [text, color] = FX[e.kind];
  app.fx.push({ text, color, cell: e.cell, at: performance.now() });
  audio.play(e.kind);
});

// ---------- modes ----------
const setMode = (mode) => {
  app.mode = mode;
  document.body.dataset.mode = mode;
  document.querySelectorAll('[data-show]').forEach((el) => { el.hidden = !el.dataset.show.split(' ').includes(mode); });
  hideBanner();
  if (mode === 'title') { app.placeId = 'midtown'; loadSandbox(7); banner('GRIDLOCK CITY', 'PRESS START'); }
  if (mode === 'arcade') loadLevel(0, { score: 0, lives: 3 });
  if (mode === 'sandbox') loadSandbox();
  if (mode === 'lab') loadLab();
  syncControls();
};

const gameOver = (why) => {
  const score = app.game.score;
  if (score > app.high) { app.high = score; try { localStorage.setItem('gridlock-city-high', String(score)); } catch { /* ignore */ } }
  app.game = { ...app.game, status: 'done' };
  audio.play('over');
  banner('GAME OVER', `${why}\nSCORE ${score} · PRESS START`);
};

// ---------- simulation step ----------
const stepSim = () => {
  const v = view();
  if (app.mode === 'arcade') {
    if (app.game.status !== 'play') return;
    const r = tick(v.net, v.sim, app.game);
    effects(r.events);
    v.sim = r.sim; app.game = r.game;
    const c = contact(v.net, v.sim, app.game); // a car may have stopped on the truck
    effects(c.events); v.sim = c.sim; app.game = c.game;
    const st = app.game.status;
    if (st === 'clear') { audio.play('clear'); const { score, lives } = app.game; banner('LEVEL CLEAR', `+2000 · TRIPS ${app.game.trips}/${app.game.quota}`, 1800); setTimeout(() => app.mode === 'arcade' && loadLevel(app.game.spec.n + 1, { score, lives }), 1800); app.game = { ...app.game, status: 'wait' }; }
    if (st === 'short') {
      const lives = app.game.lives - 1;
      if (lives <= 0) gameOver('QUOTA MISSED');
      else { audio.play('hit'); banner('QUOTA MISSED', `TRIPS ${app.game.trips}/${app.game.quota} · LIVES ${lives}`, 1800); const { score, spec } = app.game; setTimeout(() => app.mode === 'arcade' && loadLevel(spec.n, { score, lives }), 1800); app.game = { ...app.game, status: 'wait' }; }
    }
    if (st === 'gridlock') gameOver(`CITY GRIDLOCKED (≥${GRIDLOCK * 100}% FROZEN)`);
    if (st === 'over') gameOver('OUT OF TRUCKS');
  } else {
    v.sim = halfStep(v.net, v.sim, v.opts);
  }
};

// ---------- measurements ----------
const measure = () => {
  const v = view();
  const { sim, net } = v;
  const cert = certificate(net, sim, v.opts);
  const on = onStreet(sim);
  app.hist.push(sim.moved); if (app.hist.length > 2 * HZ) app.hist.shift();
  const moves = app.hist.reduce((a, b) => a + b, 0) / Math.max(1, app.hist.length / 2);
  const rho = on / net.roadCells;
  const vbar = on ? Math.min(1, moves / on) : 0;
  return { cert, on, rho, vbar, j: rho * vbar, queue: sim.pos.length - on };
};

// ---------- HUD ----------
const pct = (x) => `${Math.round(x * 100)}%`;
const hud = (m) => {
  const v = view();
  const stat = (id, val) => { const el = $(id); if (el.textContent !== val) el.textContent = val; };
  stat('s-rho', m.rho.toFixed(2)); stat('s-v', m.vbar.toFixed(2)); stat('s-j', m.j.toFixed(3));
  stat('s-frozen', v.lab ? '—' : pct(m.cert.count / Math.max(1, m.on))); stat('s-loops', String(m.cert.cores.length));
  stat('s-girth', Number.isFinite(v.girth) ? String(v.girth) : '∞'); stat('s-queue', String(m.queue));
  stat('s-signal', v.lab || v.opts.green === 1 ? 'BML' : greenAxis(v.sim.t, v.opts.green) ? 'N–S' : 'E–W');
  $('s-frozen-cell').dataset.alert = String(!v.lab && m.cert.count / Math.max(1, m.on) > 0.3);
  stat('place', v.lab ? `BML TORUS ${v.net.W}×${v.net.H}` : places.get(app.placeId)?.name ?? '');
  if (app.mode === 'arcade' && app.game) {
    const gm = app.game;
    const left = Math.max(0, Math.ceil((gm.spec.length - (v.sim.t - gm.t0)) / HZ));
    stat('h-score', String(gm.score).padStart(6, '0')); stat('h-high', String(Math.max(app.high, gm.score)).padStart(6, '0'));
    stat('h-level', String(gm.spec.n + 1)); stat('h-lives', String(Math.max(0, gm.lives)));
    stat('h-time', String(left)); stat('h-trips', `${gm.trips}/${gm.quota}`); stat('h-law', gm.spec.rules.name);
    $('h-trips').dataset.ok = String(gm.trips >= gm.quota);
  }
  if (v.lab) labReadout(m);
};

// ---------- lab: the theorems on the torus ----------
const gcd = (a, b) => (b ? gcd(b, a % b) : a);
const labReadout = (m) => {
  const { W, H } = view().net;
  const sim = view().sim;
  const n = sim.pos.length;
  const nE = sim.species.reduce((a, s) => a + (s === 1), 0);
  const gg = gcd(W, H);
  const fmax = gg >= 2 ? (W * H / gg) * Math.floor((2 * gg) / 3) : Math.max(H * Math.floor(W / 2), W * Math.floor(H / 2));
  const status = isGridlock(view().net, sim) ? 'JAM' : m.vbar >= 0.999 && app.hist.length >= 4 ? 'FREE' : 'MIXED';
  const rows = [
    ['STATE', `${status} · n = ${n} (E ${nE}, N ${n - nE}) · v̄ = ${m.vbar.toFixed(2)}`],
    ['G1', n < Math.min(W, H) ? `n < min(W,H) = ${Math.min(W, H)}: no configuration can ever gridlock.` : `n ≥ min(W,H) = ${Math.min(W, H)}: some ${n}-car gridlock exists.`],
    ['G2', n < W * H ? `n < WH: some ${n}-car configuration never gridlocks.` : 'Full torus: every configuration is frozen.'],
    ['F', `gcd(W,H) = ${gg}; the most cars that can all move every step is ${fmax}. ${n > fmax ? 'Here n exceeds it: free flow is impossible.' : 'Free flow is not ruled out.'}`],
    ['T', app.lab.rule === TRAIN ? (W === H ? (2 * n < W ? `TRAIN, 2n < N: eventual speed one is proved (Lean).` : `TRAIN square: the speed-one theorem needs 2n < N = ${W}.`) + ` A stuck TRAIN state needs W+H = ${W + H} ≤ n.` : `TRAIN: a stuck state with n cars exists iff W+H = ${W + H} ≤ n ≤ WH.`) : 'CLASSIC: the TRAIN speed-one transfer to this rule is still unproved.'],
  ];
  const html = rows.map(([k, t]) => `<dt>${k}</dt><dd>${t}</dd>`).join('');
  if ($('lab-readout').dataset.html !== html) { $('lab-readout').innerHTML = html; $('lab-readout').dataset.html = html; }
};

// ---------- fundamental diagram sweep (sandbox) ----------
const startSweep = () => {
  const v = view();
  const levels = Array.from({ length: 16 }, (_, i) => 0.05 * (i + 1));
  app.sweep = [];
  app.sweeping = { levels, i: 0 };
  $('sweep').disabled = true;
  const run = () => {
    const { i } = app.sweeping;
    if (i >= levels.length || app.mode !== 'sandbox') { app.sweeping = null; $('sweep').disabled = false; return; }
    let s = init(v.net, Math.round(v.net.roadCells * levels[i]), 99 + i, v.opts);
    let moves = 0, on = 0;
    for (let t = 0; t < 600; t++) { s = halfStep(v.net, s, v.opts); if (t >= 300) { moves += s.moved; on += onStreet(s); } }
    const rho = on / 300 / v.net.roadCells;
    app.sweep.push({ rho, j: rho * Math.min(1, (2 * moves) / Math.max(1, on)) });
    app.sweeping.i++;
    setTimeout(run, 0);
  };
  run();
};

// ---------- loop ----------
const frame = (now) => {
  const dt = Math.min(250, now - app.last); app.last = now;
  if (bannerUntil && now > bannerUntil) hideBanner();
  if (!app.paused && view()) {
    const rate = app.mode === 'arcade' ? HZ : app.speed;
    app.acc += dt * rate / 1000;
    let m = null;
    while (app.acc >= 1) { app.acc -= 1; stepSim(); m = measure(); }
    if (app.mode === 'arcade' && app.game?.status === 'play') {
      app.pacAcc += dt * 12 / 1000;
      while (app.pacAcc >= 1) {
        app.pacAcc -= 1;
        app.game = { ...app.game, player: movePlayer(view().net, app.game.player) };
        const c = contact(view().net, view().sim, app.game);
        effects(c.events); view().sim = c.sim; app.game = c.game;
      }
    }
    app.lastM = m ?? app.lastM ?? measure();
  }
  const v = view();
  if (v) {
    const m = app.lastM;
    const pl = app.mode === 'arcade' && app.game ? { ...app.game.player, safe: v.sim.t <= app.game.player.safeUntil } : null;
    drawFrame(g, { ...v, frozen: m.cert.frozen, player: pl, fx: app.fx, now });
    app.fx = app.fx.filter((e) => now - e.at < 900);
    hud(m);
    if (app.mode === 'sandbox') drawDiagram(dg, { points: app.sweep, live: { rho: m.rho, j: m.j }, w: dc.width, h: dc.height });
  }
  requestAnimationFrame(frame);
};
const dc = $('diagram');
const dg = dc.getContext('2d');

// ---------- input ----------
const KEYS = { ArrowUp: 'up', ArrowDown: 'down', ArrowLeft: 'left', ArrowRight: 'right', w: 'up', s: 'down', a: 'left', d: 'right' };
const steer = (dir) => { if (app.mode === 'arcade' && app.game) app.game = { ...app.game, player: { ...app.game.player, want: dir, dir: app.game.player.dir ?? dir } }; };
const start = () => {
  audio.unlock();
  if (app.mode === 'title' || (app.mode === 'arcade' && app.game?.status === 'done')) setMode('arcade');
};
addEventListener('keydown', (e) => {
  if (e.target.closest?.('input, select')) return;
  const dir = KEYS[e.key];
  if (dir) { steer(dir); e.preventDefault(); return; }
  if (e.key === ' ' || e.key === 'Enter') { start(); e.preventDefault(); }
  if (e.key === 'p' || e.key === 'P') app.paused = !app.paused;
  if (e.key === 'm' || e.key === 'M') toggleMute();
  if (e.key === 'Escape') setMode('title');
});
document.querySelectorAll('[data-dir]').forEach((b) => b.addEventListener('pointerdown', (e) => { e.preventDefault(); audio.unlock(); steer(b.dataset.dir); }));
let touch0 = null;
canvas.addEventListener('pointerdown', (e) => { touch0 = [e.clientX, e.clientY]; });
canvas.addEventListener('pointerup', (e) => {
  if (!touch0) return;
  const [dx, dy] = [e.clientX - touch0[0], e.clientY - touch0[1]];
  touch0 = null;
  if (Math.hypot(dx, dy) < 20) { start(); return; }
  steer(Math.abs(dx) > Math.abs(dy) ? (dx > 0 ? 'right' : 'left') : (dy > 0 ? 'down' : 'up'));
});
const toggleMute = () => { audio.setMuted(!audio.isMuted()); $('mute').textContent = audio.isMuted() ? 'SOUND OFF' : 'SOUND ON'; };
$('mute').addEventListener('click', () => { audio.unlock(); toggleMute(); });
document.querySelectorAll('[data-mode]').forEach((b) => b.addEventListener('click', () => { audio.unlock(); setMode(b.dataset.mode); }));
$('start').addEventListener('click', start);

// ---------- controls ----------
const placeSel = $('c-place');
const fillPlaces = () => {
  placeSel.innerHTML = [...places.values()].map((p) => `<option value="${p.id}">${p.name}</option>`).join('');
  placeSel.value = app.placeId;
};
fillPlaces();
const syncControls = () => {
  placeSel.value = app.placeId;
  $('c-rule').value = app.opts.rule; $('c-green').value = app.opts.green; $('c-box').checked = app.opts.box;
  $('c-cross').checked = app.opts.crossTurns; $('c-rho').value = app.rho; $('c-slow').value = app.opts.slow; $('c-speed').value = app.speed;
  $('c-green-v').textContent = app.opts.green === 1 ? 'BML' : String(app.opts.green);
  $('c-rho-v').textContent = app.rho.toFixed(2); $('c-slow-v').textContent = app.opts.slow.toFixed(2); $('c-speed-v').textContent = `${app.speed}/s`;
  $('l-w').value = app.lab.W; $('l-h').value = app.lab.H; $('l-p').value = app.lab.p; $('l-rule').value = app.lab.rule;
  $('l-p-v').textContent = app.lab.p.toFixed(2);
};
const onSandbox = (fn, reset = true) => (e) => { fn(e.target); syncControls(); if (app.mode === 'sandbox') { if (reset) loadSandbox(); else view().opts = app.opts; } };
placeSel.addEventListener('change', onSandbox((t) => { app.placeId = t.value; }));
$('c-rule').addEventListener('change', onSandbox((t) => { app.opts = { ...app.opts, rule: t.value }; }, false));
$('c-green').addEventListener('input', onSandbox((t) => { app.opts = { ...app.opts, green: +t.value }; }, false));
$('c-box').addEventListener('change', onSandbox((t) => { app.opts = { ...app.opts, box: t.checked }; }, false));
$('c-cross').addEventListener('change', onSandbox((t) => { app.opts = { ...app.opts, crossTurns: t.checked }; }, false));
$('c-slow').addEventListener('input', onSandbox((t) => { app.opts = { ...app.opts, slow: +t.value }; }, false));
$('c-rho').addEventListener('change', onSandbox((t) => { app.rho = +t.value; }));
$('c-rho').addEventListener('input', (e) => { $('c-rho-v').textContent = (+e.target.value).toFixed(2); });
$('c-speed').addEventListener('input', (e) => { app.speed = +e.target.value; syncControls(); });
$('reset').addEventListener('click', () => loadSandbox(1 + Math.floor(Math.random() * 1e6)));
$('incident').addEventListener('click', () => {
  const v = view();
  const live = [...v.sim.pos.keys()].filter((k) => v.sim.pos[k] >= 0 && !isStalled(v.sim, k));
  if (!live.length) return;
  const k = live[Math.floor(Math.random() * live.length)];
  v.sim = breakDown(v.sim, k, 200);
  effects([{ kind: 'breakdown', cell: v.sim.pos[k] }]);
});
$('sweep').addEventListener('click', startSweep);
$('presets-law').addEventListener('change', (e) => {
  const r = RULESETS.find((x) => x.name === e.target.value);
  if (r) { app.opts = { ...app.opts, green: r.green, box: r.box, crossTurns: r.crossTurns }; syncControls(); if (app.mode === 'sandbox') view().opts = app.opts; }
});
$('presets-law').innerHTML = `<option value="">Traffic law…</option>${RULESETS.map((r) => `<option>${r.name}</option>`).join('')}`;

const labChange = (fn) => (e) => { fn(e.target); syncControls(); if (app.mode === 'lab') loadLab(); };
$('l-w').addEventListener('change', labChange((t) => { app.lab.W = Math.max(1, Math.min(96, +t.value || 1)); }));
$('l-h').addEventListener('change', labChange((t) => { app.lab.H = Math.max(1, Math.min(64, +t.value || 1)); }));
$('l-p').addEventListener('change', labChange((t) => { app.lab.p = +t.value; }));
$('l-p').addEventListener('input', (e) => { $('l-p-v').textContent = (+e.target.value).toFixed(2); });
$('l-rule').addEventListener('change', labChange((t) => { app.lab.rule = t.value; }));
$('l-reset').addEventListener('click', () => { app.lab.seed++; loadLab(); });

// live place loading
$('find').addEventListener('submit', async (e) => {
  e.preventDefault();
  const q = $('c-where').value.trim();
  if (!q) return;
  const say = (t) => { $('find-msg').textContent = t; };
  try {
    say('Finding the place…');
    const centre = await locate(q);
    say(`Downloading streets around ${centre.name}…`);
    const roads = await fetchRoads(centre);
    if (roads.length < 3) throw new Error('Too few drivable streets in this window. Try a busier spot.');
    const id = `live-${Date.now()}`;
    places.set(id, { id, name: centre.name.slice(0, 22), lat: centre.lat, lon: centre.lon, drive: driveSide(centre), roads });
    fillPlaces(); app.placeId = id; setMode('sandbox');
    say(`Loaded ${roads.length} streets. Map data © OpenStreetMap contributors.`);
  } catch (err) {
    say(`${err.message?.includes('fetch') || err.name === 'TypeError' ? 'This page cannot reach OpenStreetMap from here. Run the app locally (app/README.md) to load any place.' : err.message}`);
  }
});

// ---------- layout: integer pixel scaling ----------
const fit = () => {
  const box = $('stage').clientWidth;
  const k = box >= CW ? Math.floor(box / CW) : box / CW;
  canvas.style.width = `${CW * k}px`; canvas.style.height = `${CH * k}px`;
};
addEventListener('resize', fit);
fit();

setMode('title');
requestAnimationFrame(frame);
