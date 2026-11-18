// Blocker certificates — the map analogue of Lemma G0 and Theorem G1 (docs/theorems.md).
//
// β(k) is the car that keeps k from moving: the occupant of k's committed next cell, or — under
// the box rule, when k waits to enter a junction — the first occupant along its committed path
// through the box. A car only re-plans after it moves, so if β(k) never moves, neither does k.
// Hence on a β-cycle (induction on the first time any of its cars moves):
//   CLASSIC: no car of the cycle ever moves again;
//   TRAIN:   the same, unless the cycle is all direct edges of one axis (a ring that rotates).
// Every car whose β-path reaches such a cycle is frozen too. Signals and the slow-down only
// remove moves, so they cannot break a certificate. A direct β-cycle is a directed cycle of the
// lane graph on distinct cars, hence has ≥ girth cars.
import { TRAIN, DEFAULTS, aheadOf } from './sim.js';

/** [blocker, direct?] for car k, or [−1, false] if k is not blocked by a car. */
export const blockerOf = (net, s, k, box) => {
  if (s.pos[k] < 0 || s.next[k] < 0) return [-1, false];
  const j = s.occ[s.next[k]];
  if (j >= 0) return [j, true];
  if (!box || !net.junction[s.next[k]] || net.junction[s.pos[k]]) return [-1, false];
  const c = aheadOf(s, k).find((x) => x >= 0 && s.occ[x] >= 0);
  return c === undefined ? [-1, false] : [s.occ[c], false];
};

/** { frozen: Uint8Array (0 free, 1 captured, 2 core), cores: [[car…]], count } */
export const certificate = (net, s, opts = DEFAULTS) => {
  const N = s.pos.length;
  const beta = new Int32Array(N);
  const direct = new Uint8Array(N);
  for (let k = 0; k < N; k++) [beta[k], direct[k]] = blockerOf(net, s, k, opts.box);
  const frozen = new Uint8Array(N);
  const color = new Uint8Array(N); // 0 unseen, 1 on path, 2 done
  const cores = [];
  for (let k0 = 0; k0 < N; k0++) {
    if (color[k0]) continue;
    const path = [];
    let k = k0, mark = 0;
    while (k >= 0 && !color[k]) { color[k] = 1; path.push(k); k = beta[k]; }
    if (k >= 0 && color[k] === 1) {
      const cycle = path.slice(path.indexOf(k));
      const rotates = opts.rule === TRAIN && cycle.every((c) => direct[c] && s.axis[c] === s.axis[cycle[0]]);
      if (!rotates) { cores.push(cycle); cycle.forEach((c) => { frozen[c] = 2; }); mark = 1; }
    } else if (k >= 0) mark = frozen[k] ? 1 : 0;
    path.forEach((p) => { color[p] = 2; if (!frozen[p]) frozen[p] = mark; });
  }
  return { frozen, cores, count: frozen.reduce((a, f) => a + (f > 0), 0) };
};

/** Every car on the street is directly blocked: with no slow-down, a fixed point (Lemma G0). */
export const isGridlock = (net, s) => {
  let any = false;
  for (let k = 0; k < s.pos.length; k++) {
    if (s.pos[k] < 0) continue;
    if (!blockerOf(net, s, k, false)[1]) return false;
    any = true;
  }
  return any;
};

/** Cars currently on the street. */
export const onStreet = (s) => s.pos.reduce((a, p) => a + (p >= 0), 0);
