// Theorems for real traffic flow: results that drop the lattice model's idealisations.
// Proofs: docs/research/2026-11-24-real-traffic-theorems.md.
//
//   trapSet          R2: permanent gridlock when drivers may re-route (OR-model deadlock)
//   safeCells        R2: cells that can never hold a trapped car, whoever occupies them
//   jamGirthMetres   R1: minimum gridlock size from physical loop length and jam spacing
//   closureTimeBound R3: earliest time a loop can lock, from mass conservation
//   mfdEnvelope      R5: Little's law + speed limit + cut capacity bound network flow
import { turnOptions, EXIT, aheadOf } from './sim.js';

/** Options of car k, each as the list of cells that must be free for that move. Re-routing drivers
 * may take any legal option from their current lane, unless committed through a junction box;
 * committed drivers have one option. Under the box rule, entering a junction from outside also
 * needs the committed path through the box free (sim.boxClear). */
const optionsOf = (net, s, k, opts, reroute) => {
  const needs = (c) => (c >= 0 && opts.box && net.junction[c] && !net.junction[s.pos[k]] && c === s.next[k]
    ? [c, ...aheadOf(s, k).filter((x) => x >= 0)] : [c]);
  return reroute && !s.aheadLen[k] && !s.species[k]
    ? turnOptions(net, s.pos[k], s.prev[k], opts).cells.map((c) => [c])
    : [needs(s.next[k])];
};

/** R2. The greatest trap: the largest set S of cars on the street such that every option of every
 * car in S needs some cell occupied by a car in S (EXIT is never blocked). Under CLASSIC no car of
 * S ever moves again, whatever its driver chooses. Computed by deleting cars that have a free,
 * exiting or untrapped option until nothing changes (a greatest fixed point; the union of traps
 * is a trap). */
export const trapSet = (net, s, opts, { reroute = false } = {}) => {
  const N = s.pos.length;
  const inS = Uint8Array.from({ length: N }, (_, k) => (s.pos[k] >= 0 ? 1 : 0)); // breakdowns only remove moves
  const options = Array.from({ length: N }, (_, k) => (inS[k] ? optionsOf(net, s, k, opts, reroute) : []));
  const free = (c) => c === EXIT || s.occ[c] < 0 || !inS[s.occ[c]];
  const escapes = (k) => options[k].length === 0 || options[k].some((need) => need.every(free));
  for (let changed = true; changed;) {
    changed = false;
    for (let k = 0; k < N; k++) if (inS[k] && escapes(k)) { inS[k] = 0; changed = true; }
  }
  return inS;
};

/** R2 (no box rule). Safe cells: the least set such that a cell is safe when, for every way a car can arrive in
 * it (every in-lane, and a spawn where cars spawn), its options include EXIT or a safe cell. A
 * re-routing driver in a safe cell is never trapped; if every road cell is safe, no configuration
 * ever contains a trap. Returns { safe: Uint8Array, count, roadCells }. */
export const safeCells = (net, opts) => {
  // Under the box rule a car committed through a box cannot re-route and its entry needs a whole
  // path free, so "some option is safe" no longer implies escape: the theorem does not apply.
  if (opts.box) throw new Error('safeCells: the safe-cell theorem assumes no box rule');
  const n = net.W * net.H;
  const spawn = new Set(net.entries.length ? net.entries : []);
  const arrivals = (c) => [...net.inList.subarray(net.inStart[c], net.inStart[c + 1]), ...(spawn.has(c) || !net.entries.length ? [-1] : [])];
  const optionSets = new Map();
  for (let c = 0; c < n; c++)
    if (net.road[c]) optionSets.set(c, arrivals(c).map((a) => turnOptions(net, c, a, opts).cells));
  const safe = new Uint8Array(n);
  for (let changed = true; changed;) {
    changed = false;
    for (const [c, sets] of optionSets)
      if (!safe[c] && sets.every((cells) => cells.some((x) => x === EXIT || safe[x]))) { safe[c] = 1; changed = true; }
  }
  return { safe, count: safe.reduce((a, b) => a + b, 0), roadCells: net.roadCells };
};

/** R1. Fewest vehicles in a gridlock around a committed loop of physical length L (m), with jam
 * spacing sJam (m, front-to-front at standstill): ⌈L / sJam⌉. */
export const minGridlockVehicles = (loopMetres, sJam = 7.5) => Math.ceil(loopMetres / sJam - 1e-9);

/** R1 on a lane graph: girth in cells × cell length = the shortest committed loop in metres. */
export const jamGirthMetres = (girthCells, cellMetres) => girthCells * cellMetres;

/** R3. A loop of length L (m) holding n0 vehicles cannot lock before
 * (L / sJam − n0) / inflowCapacity, where inflowCapacity (veh/s) bounds the net inflow into it. */
export const closureTimeBound = ({ loopMetres, n0, inflowCapacity, sJam = 7.5 }) =>
  Math.max(0, (loopMetres / sJam - n0) / inflowCapacity);

/** R5. Upper envelope of the network flow (trips completed per unit time) at mean accumulation N:
 * min(N · vFree / meanTrip, cutCapacity). */
export const mfdEnvelope = ({ accumulation, vFree, meanTrip, cutCapacity }) =>
  Math.min((accumulation * vFree) / meanTrip, cutCapacity);
