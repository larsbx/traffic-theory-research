// Arcade rules as pure reducers over (net, sim state, game state).
//
// You drive a tow truck. Certified-frozen cars (src/analysis.js) and broken-down cars may be
// towed; nothing else can. Breaking a β-cycle frees everything captured behind it. A moving
// car that drives into you costs a life. Each level is a real place with a trip quota; every
// six levels the city repeals one traffic law.
import { tow, isStalled, breakDown, halfStep, init, CLASSIC } from './sim.js';
import { certificate, onStreet } from './analysis.js';
import { makeRng } from './rng.js';

export const RULESETS = Object.freeze([
  { name: 'CITY CODE', green: 6, box: true, crossTurns: false },
  { name: 'FREE TURNS', green: 6, box: true, crossTurns: true },
  { name: 'BLOCK THE BOX', green: 6, box: false, crossTurns: true },
  { name: 'BML LIGHTS', green: 1, box: false, crossTurns: true },
]);
export const ORDER = Object.freeze(['grachten', 'midtown', 'eixample', 'bank', 'etoile', 'shibuya']);
export const POINTS = Object.freeze({ exit: 10, incident: 300, core: 500, captured: 100, clear: 2000 });
export const HZ = 10; // half-steps per second
export const TOW_DELAY = 20; // half-steps before a towed car re-enters
export const GRIDLOCK = 0.6; // frozen share of on-street cars that ends the game

/** Level n (0-based): place, traffic law, density, incident cadence — all in half-steps. */
export const levelSpec = (n) => {
  const loop = Math.floor(n / ORDER.length);
  return Object.freeze({
    n,
    place: ORDER[n % ORDER.length],
    rules: Object.freeze({ ...RULESETS[Math.min(loop, RULESETS.length - 1)], rule: CLASSIC, slow: 0.1, respawnDelay: 0 }),
    rho: Math.min(0.18 + 0.03 * (n % ORDER.length) + 0.06 * loop, 0.6),
    length: 75 * HZ,
    incidentEvery: Math.max(40, 140 - 8 * n),
    incidentLength: 150 + 10 * n,
  });
};

export const DIRS = Object.freeze({ up: [0, 1], down: [0, -1], left: [-1, 0], right: [1, 0] });

const stepCell = (net, cell, dir) => {
  if (!dir) return -1;
  const [dx, dy] = DIRS[dir];
  const [x, y] = [(cell % net.W) + dx, Math.floor(cell / net.W) + dy];
  return x >= 0 && y >= 0 && x < net.W && y < net.H && net.road[y * net.W + x] ? y * net.W + x : -1;
};

/** Pac-Man steering: take the wanted turn as soon as the road allows, else keep going. */
export const movePlayer = (net, p) => {
  const turned = stepCell(net, p.cell, p.want);
  if (turned >= 0) return { ...p, cell: turned, dir: p.want };
  const ahead = stepCell(net, p.cell, p.dir);
  return ahead >= 0 ? { ...p, cell: ahead } : p;
};

/** Road cell closest to the centre (the depot). */
export const depot = (net) => {
  const [cx, cy] = [net.W / 2, net.H / 2];
  let best = -1, bd = Infinity;
  for (let c = 0; c < net.W * net.H; c++) {
    const d = Math.hypot((c % net.W) - cx, Math.floor(c / net.W) - cy);
    if (net.road[c] && d < bd) [best, bd] = [c, d];
  }
  return best;
};

/** Trips a city completes in one level with no incidents, from a headless run. */
export const baseline = (net, spec, seed) => {
  let s = init(net, Math.round(net.roadCells * spec.rho), seed, spec.rules);
  for (let t = 0; t < spec.length; t++) s = halfStep(net, s, spec.rules);
  return s.exited;
};

export const newLevel = (net, spec, prev = { score: 0, lives: 3 }, seed = 1) => {
  const sim = init(net, Math.round(net.roadCells * spec.rho), seed, spec.rules);
  return {
    sim,
    game: Object.freeze({
      spec, seed, score: prev.score, lives: prev.lives, t0: sim.t, exits0: sim.exited, trips: 0, status: 'play',
      quota: Math.max(10, Math.round(0.55 * baseline(net, spec, seed + 1))),
      player: Object.freeze({ cell: depot(net), dir: null, want: null, safeUntil: sim.t + 3 * HZ }),
    }),
  };
};

/** Tow whatever certified car the truck is on. Returns { sim, game, events }. */
export const contact = (net, sim, game) => {
  const k = sim.occ[game.player.cell];
  if (k < 0) return { sim, game, events: [] };
  const { frozen } = certificate(net, sim, game.spec.rules);
  const kind = isStalled(sim, k) ? 'incident' : frozen[k] === 2 ? 'core' : frozen[k] === 1 ? 'captured' : null;
  if (!kind) return { sim, game, events: [] };
  return {
    sim: tow(sim, k, TOW_DELAY),
    game: { ...game, score: game.score + POINTS[kind] },
    events: [{ kind, cell: game.player.cell, points: POINTS[kind] }],
  };
};

/** Advance the city one half-step: incidents, traffic, collisions, end-of-level checks. */
export const tick = (net, sim0, game) => {
  const { spec } = game;
  const elapsed = sim0.t - game.t0;
  const rng = makeRng(sim0.seed ^ 0x9e3779b9);
  let sim = sim0;
  const events = [];
  if (elapsed > 0 && elapsed % spec.incidentEvery === 0) {
    const live = [...sim.pos.keys()].filter((k) => sim.pos[k] >= 0 && !isStalled(sim, k));
    if (live.length) {
      const k = rng.pick(live);
      sim = breakDown(sim, k, spec.incidentLength);
      events.push({ kind: 'breakdown', cell: sim.pos[k], points: 0 });
    }
  }
  const next = halfStep(net, sim, spec.rules);
  let g = { ...game, score: game.score + POINTS.exit * (next.exited - sim.exited) };
  const hitBy = next.occ[g.player.cell];
  if (hitBy >= 0 && next.last[hitBy] === sim.t && next.t > g.player.safeUntil) {
    events.push({ kind: 'hit', cell: g.player.cell, points: 0 });
    g = { ...g, lives: g.lives - 1, player: { ...g.player, cell: depot(net), dir: null, want: null, safeUntil: next.t + 3 * HZ } };
  }
  const { count } = certificate(net, next, spec.rules);
  const share = count / Math.max(1, onStreet(next));
  const trips = next.exited - game.exits0;
  const status = g.lives <= 0 ? 'over' : share >= GRIDLOCK && onStreet(next) > 20 ? 'gridlock'
    : next.t - g.t0 >= spec.length ? (trips >= g.quota ? 'clear' : 'short') : 'play';
  if (status === 'clear') g = { ...g, score: g.score + POINTS.clear };
  return { sim: next, game: { ...g, status, trips }, events };
};
