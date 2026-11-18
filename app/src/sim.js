// Two-phase cellular automaton on a lane graph — BML generalised to real streets.
//
// Each car k sits in a cell pos[k] with a committed next cell next[k] (or EXIT), chosen when it
// arrives. The axis of that move (0 horizontal, 1 vertical) is its species for the current hop.
// Half-steps alternate phase 0, 1, 0, … — BML's east-then-north order, and a two-phase signal at
// every junction. In phase φ only cars whose committed move has axis φ may move:
//
//   CLASSIC  move iff the target cell is empty before the half-step (BML 1992, Model I);
//   TRAIN    move iff the target is empty or its occupant also moves; closed loops of
//            same-phase cars rotate (Austin–Benjamini 2006).
//
// Junction cells carry a signal: a move INTO a junction is allowed only while green(t) equals
// its axis, green(t) = ⌊t / G⌋ mod 2 for a green time of G half-steps. G = 1 makes the signal
// coincide with the phase, so it never binds — pure BML. Longer G empties the box between
// phases, which is what keeps the 2×2 box of a two-way crossing from locking.
//
// Box rule ("don't block the box", opts.box): a car outside a junction commits to its whole
// path through the junction box and may enter only if every cell of that path, up to and
// including the first cell beyond the box, is empty. Queues then spill back before the box,
// never into it.
//
// Where several cars contend for one cell (merges — impossible on the BML torus) the one that
// has waited longest wins, ties to the lower id. A broken-down car (breakDown) does not move. On `torus(W, H)` with fixed species 1 = E and
// 2 = N this is exactly `bml.model.step` (see test/sim.test.js). All functions are pure.
import { makeRng } from './rng.js';
import { axisOf, edgeHeading } from './raster.js';

export const EXIT = -2;
export const CLASSIC = 'classic';
export const TRAIN = 'train';
export const DEFAULTS = Object.freeze({ rule: CLASSIC, slow: 0, crossTurns: true, straight: 4, respawnDelay: 0, green: 1, box: false });
export const AHEAD = 6; // longest committed path through a junction box

/** Named traffic laws, from realistic to bare BML. */
export const LAWS = Object.freeze([
  { name: 'CITY CODE', green: 6, box: true, crossTurns: false },
  { name: 'FREE TURNS', green: 6, box: true, crossTurns: true },
  { name: 'BLOCK THE BOX', green: 6, box: false, crossTurns: true },
  { name: 'BML LIGHTS', green: 1, box: false, crossTurns: true },
]);

/** Axis currently allowed to enter junctions at half-step t. */
export const greenAxis = (t, green) => Math.floor(t / green) & 1;

/** Signed turn angle a→b→c in (−π, π], from the lanes' street headings (staircase steps of a
 * diagonal street are not turns). Positive = left. */
export const turnAngle = (net, a, b, c) => {
  const d = edgeHeading(net, b, c) - edgeHeading(net, a, b);
  return Math.atan2(Math.sin(d), Math.cos(d));
};
const STRAIGHT = Math.PI / 6;
const MAX_TURN = (2 * Math.PI) / 3; // sharper is a U-turn through a fork: allowed only at dead ends
const REVERSAL = (5 * Math.PI) / 6; // two hops turning this far in total are a U-turn in two steps
const angleDiff = (a, b) => Math.abs(Math.atan2(Math.sin(a - b), Math.cos(a - b)));
const isStraight = (net, a, b, c) => Math.abs(turnAngle(net, a, b, c)) < STRAIGHT;

/** Is a→b→c a turn across oncoming traffic (left under right-hand drive, right under left)? */
export const crossesTraffic = (net, a, b, c) => (net.drive === 'L' ? -1 : 1) * turnAngle(net, a, b, c) > STRAIGHT;

/** The hop after `cell`, having arrived from `prev` (−1 if spawned) with heading h0 on the hop
 * before that (NaN if unknown): a cell or EXIT. */
const hop = (net, cell, prev, species, rng, opts, h0 = NaN) => {
  const { W, H } = net;
  if (species === 1) return Math.floor(cell / W) * W + ((cell % W) + 1) % W;
  if (species === 2) return (Math.floor(cell / W) + 1) % H * W + (cell % W);
  const all = [...net.outList.subarray(net.outStart[cell], net.outStart[cell + 1])];
  const noU = prev < 0 ? all : all.filter((c) => c !== prev && Math.abs(turnAngle(net, prev, cell, c)) <= MAX_TURN &&
    !(angleDiff(edgeHeading(net, cell, c), h0) > REVERSAL));
  const fwd = noU.length ? noU : all;
  const legal = prev < 0 || opts.crossTurns ? fwd : fwd.filter((c) => !crossesTraffic(net, prev, cell, c));
  const options = [...(legal.length ? legal : fwd), ...(net.exit[cell] ? [EXIT] : [])];
  if (!options.length) return EXIT;
  const straight = (c) => prev >= 0 && c >= 0 && isStraight(net, prev, cell, c);
  return rng.weighted(options, options.map((c) => (straight(c) ? opts.straight : 1)));
};

/** Committed route from `cell`: the next hop, then (box rule) the rest of the way through a box. */
export const plan = (net, cell, prev, species, rng, opts, h0 = NaN) => {
  const route = [hop(net, cell, prev, species, rng, opts, h0)];
  if (!opts.box || species || net.junction[cell]) return route;
  for (let [z, a, b] = [prev, cell, route[0]]; b >= 0 && net.junction[b] && route.length <= AHEAD; [z, a, b] = [a, b, route.at(-1)])
    route.push(hop(net, b, a, species, rng, opts, z >= 0 ? edgeHeading(net, z, a) : NaN));
  return route;
};

/** Axis of the hop cell → next; an exit keeps the axis of arrival. */
const axisFor = (net, cell, prev, next) => (next >= 0 ? axisOf(net, cell, next) : prev >= 0 ? axisOf(net, prev, cell) : 0);

const empty = (net, n, seed) => ({
  t: 0, seed: seed >>> 0, moved: 0, exited: 0,
  occ: new Int32Array(net.W * net.H).fill(-1),
  pos: new Int32Array(n).fill(-1), next: new Int32Array(n).fill(EXIT), prev: new Int32Array(n).fill(-1),
  axis: new Int8Array(n), wait: new Int32Array(n), last: new Int32Array(n).fill(-1),
  hold: new Int32Array(n), species: new Int8Array(n),
  ahead: new Int32Array(n * AHEAD).fill(EXIT), aheadLen: new Int8Array(n),
  stall: new Int32Array(n), // broken down until this half-step
});

const setRoute = (net, s, k, cell, prev, route) => {
  s.next[k] = route[0];
  s.axis[k] = s.species[k] ? s.species[k] - 1 : axisFor(net, cell, prev, route[0]); // BML species fix the axis (even on self-loops)
  s.aheadLen[k] = route.length - 1;
  route.slice(1).forEach((c, i) => { s.ahead[k * AHEAD + i] = c; });
};

/** The committed cells after next[k] (box path), as a fresh array. */
export const aheadOf = (s, k) => [...s.ahead.subarray(k * AHEAD, k * AHEAD + s.aheadLen[k])];

const place = (net, s, k, cell, prev, rng, opts) => {
  const h0 = prev >= 0 && s.prev[k] >= 0 && s.pos[k] === prev ? edgeHeading(net, s.prev[k], prev) : NaN;
  s.occ[cell] = k; s.pos[k] = cell; s.prev[k] = prev; s.wait[k] = 0;
  const pending = aheadOf(s, k);
  setRoute(net, s, k, cell, prev, pending.length ? pending : plan(net, cell, prev, s.species[k], rng, opts, h0));
};

/** n roaming cars on distinct random cells, each with a random arrival direction. */
export const init = (net, n, seed, opts = DEFAULTS) => {
  const rng = makeRng(seed);
  const cells = [...net.road.keys()].filter((c) => net.road[c] && net.outStart[c + 1] > net.outStart[c]);
  for (let i = cells.length - 1; i > 0; i--) { const j = rng.int(i + 1); [cells[i], cells[j]] = [cells[j], cells[i]]; }
  const s = empty(net, Math.min(n, cells.length), seed);
  cells.slice(0, s.pos.length).forEach((c, k) => {
    const ins = net.inList.subarray(net.inStart[c], net.inStart[c + 1]);
    place(net, s, k, c, ins.length ? rng.pick(ins) : -1, rng, opts);
  });
  return { ...s, seed: rng.seed() };
};

/** A BML configuration grid[y][x] ∈ {0 empty, 1 east, 2 north} on `torus(W, H)`. */
export const fromGrid = (net, grid) => {
  const cars = grid.flatMap((row, y) => row.flatMap((v, x) => (v ? [[y * net.W + x, v]] : [])));
  const s = empty(net, cars.length, 1);
  cars.forEach(([c, v], k) => { s.species[k] = v; place(net, s, k, c, -1, null, DEFAULTS); });
  return s;
};

export const toGrid = (net, s) =>
  Array.from({ length: net.H }, (_, y) => Array.from({ length: net.W }, (_, x) => {
    const k = s.occ[y * net.W + x];
    return k < 0 ? 0 : s.species[k];
  }));

const clone = (s) => ({
  ...s,
  occ: s.occ.slice(), pos: s.pos.slice(), next: s.next.slice(), prev: s.prev.slice(), axis: s.axis.slice(),
  wait: s.wait.slice(), last: s.last.slice(), hold: s.hold.slice(), species: s.species,
  ahead: s.ahead.slice(), aheadLen: s.aheadLen.slice(), stall: s.stall.slice(),
});

/** Box rule: entering a junction from outside needs the committed path through it clear. */
export const boxClear = (net, s, k) => {
  if (!net.junction[s.next[k]] || net.junction[s.pos[k]]) return true;
  return aheadOf(s, k).every((c) => c < 0 || s.occ[c] < 0);
};

/** Which contenders move this half-step: Uint8Array over cars. */
const movers = (s, want, rule) => {
  const N = s.pos.length;
  const winner = new Map();
  for (let k = 0; k < N; k++) {
    const c = want[k];
    if (c < 0 || (rule === CLASSIC && s.occ[c] >= 0)) continue;
    const w = winner.get(c);
    if (w === undefined || s.wait[k] > s.wait[w]) winner.set(c, k); // ids ascend, so ties keep the lower id
  }
  const wins = (k) => want[k] === EXIT || (want[k] >= 0 && winner.get(want[k]) === k);
  const out = new Uint8Array(N);
  if (rule === CLASSIC) { for (let k = 0; k < N; k++) out[k] = wins(k); return out; }

  // TRAIN: winners have distinct targets, so winner→occupant chains are paths or cycles.
  const state = new Int8Array(N); // 0 unknown, 1 on current path, 2 moves, 3 stays
  for (let k0 = 0; k0 < N; k0++) {
    if (state[k0] || !wins(k0)) continue;
    const path = [];
    let k = k0, res;
    for (;;) {
      if (state[k] === 1) { res = true; break; } // closed loop: rotates
      if (state[k] > 1) { res = state[k] === 2; break; }
      if (!wins(k)) { res = false; break; }
      state[k] = 1; path.push(k);
      if (want[k] === EXIT) { res = true; break; }
      const j = s.occ[want[k]];
      if (j < 0) { res = true; break; }
      k = j;
    }
    path.forEach((p) => { state[p] = res ? 2 : 3; out[p] = res; });
  }
  return out;
};

/** One half-step in phase t mod 2. Returns the new state; `moved`/`exited` describe it. */
export const halfStep = (net, s0, opts = DEFAULTS) => {
  const o = { ...DEFAULTS, ...opts };
  const rng = makeRng(s0.seed);
  const phase = s0.t & 1;
  const red = greenAxis(s0.t, o.green) !== phase;
  const N = s0.pos.length;
  const want = new Int32Array(N).fill(-3);
  for (let k = 0; k < N; k++)
    if (s0.pos[k] >= 0 && s0.axis[k] === phase && s0.stall[k] <= s0.t && !(red && s0.next[k] >= 0 && net.junction[s0.next[k]]) &&
        !(o.box && s0.next[k] >= 0 && !boxClear(net, s0, k)) &&
        !(o.slow > 0 && s0.species[k] === 0 && rng.float() < o.slow))
      want[k] = s0.next[k];
  const go = movers(s0, want, o.rule);

  const s = clone(s0);
  let moved = 0, exited = 0;
  for (let k = 0; k < N; k++) if (go[k]) s.occ[s0.pos[k]] = -1;
  for (let k = 0; k < N; k++) {
    if (!go[k]) { if (want[k] !== -3) s.wait[k]++; continue; }
    moved++;
    s.last[k] = s0.t;
    if (want[k] === EXIT) { exited++; s.pos[k] = -1; s.hold[k] = s0.t + o.respawnDelay; s.aheadLen[k] = 0; continue; }
    place(net, s, k, want[k], s0.pos[k], rng, o);
  }
  // Closed system: cars that left re-enter at a free map entry (car count is conserved).
  const doors = net.entries.length ? net.entries : null;
  for (let k = 0; k < N; k++) {
    if (s.pos[k] >= 0 || s.hold[k] > s0.t || s.species[k]) continue;
    const c = doors ? rng.pick(doors) : rng.int(net.W * net.H);
    if (net.road[c] && s.occ[c] < 0 && net.outStart[c + 1] > net.outStart[c]) place(net, s, k, c, -1, rng, o);
  }
  return { ...s, t: s0.t + 1, seed: rng.seed(), moved, exited: s0.exited + exited };
};

/** A full BML step: both phases. */
export const step = (net, s, opts) => halfStep(net, halfStep(net, s, opts), opts);

/** Car k breaks down for `duration` half-steps (an incident: it blocks its lane meanwhile). */
export const breakDown = (s0, k, duration) => {
  const s = clone(s0);
  s.stall[k] = s0.t + duration;
  return s;
};

export const isStalled = (s, k) => s.pos[k] >= 0 && s.stall[k] > s.t;

/** Remove car k from the street (it re-enters later at a map entry). */
export const tow = (s0, k, delay = 0) => {
  if (s0.pos[k] < 0) return s0;
  const s = clone(s0);
  s.occ[s0.pos[k]] = -1;
  s.pos[k] = -1;
  s.hold[k] = s0.t + delay;
  s.aheadLen[k] = 0;
  s.stall[k] = 0;
  return s;
};
