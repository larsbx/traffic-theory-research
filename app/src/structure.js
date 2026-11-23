// Dynamics-free structure of a lane graph: what the repository's mathematics says about a real
// map without running any update rule. Proofs: docs/research/2026-11-23-dynamics-free-map-mathematics.md
//
//   jamGraph      J: arc b→c iff some car at b may commit to c (sim.turnOptions, or a spawn)
//   girthOf       shortest directed cycle; under (E)+(C) every direct jam core has ≥ girth(J) cars
//   cycleCensus   simple cell-cycles of L up to a length, with routing weights π(C)
//   cycleRisk     Σ_C ρ^|C| π(C): mean-field index of instantaneously closed blocking loops
//   spectralRadius  λ_max of the substochastic turning matrix P (exits leak mass)
//   throughputBound  max-flow from entries to exits with per-cell capacities in cars per full step
//   cuttingWord / freeSpeed   Sturmian axis words of straight streets and their free speed
import { turnOptions, EXIT, CLASSIC } from './sim.js';
import { traverse } from './raster.js';

/** Cells where a car can appear with no arrival direction: map entries (or, on a map without
 * entries, every cell — the simulator's fallback). Such a car may take any outgoing lane. */
export const spawnCells = (net) => (net.entries.length ? new Set(net.entries) : new Set([...net.road.keys()].filter((c) => net.road[c])));

/** The jam graph J on road cells: an arc b → c whenever some car at b can commit to c — for
 * some arrival a (sim.turnOptions), or freshly spawned. A β-cycle is a cycle of committed hops
 * by different cars, each with its own arrival, so J (not a single car's turn graph) is where
 * jam cores live. p is the mean-field routing probability P(next = c | at b), averaging over
 * the in-lanes uniformly; spawn-only arcs carry p = 0. Mass to EXIT is dropped (substochastic). */
export const jamGraph = (net, opts) => {
  const spawn = spawnCells(net);
  const cells = [...net.road.keys()].filter((c) => net.road[c]);
  const at = new Map(cells.map((c, i) => [c, i]));
  const succ = cells.map((b) => {
    const ins = [...net.inList.subarray(net.inStart[b], net.inStart[b + 1])];
    const p = new Map();
    for (const a of ins.length ? ins : [-1]) {
      const { cells: opt, weights } = turnOptions(net, b, a, opts);
      const total = weights.reduce((x, y) => x + y, 0);
      opt.forEach((c, k) => { if (c !== EXIT) p.set(c, (p.get(c) ?? 0) + weights[k] / total / Math.max(1, ins.length)); });
    }
    if (spawn.has(b)) for (const c of net.outList.subarray(net.outStart[b], net.outStart[b + 1])) if (!p.has(c)) p.set(c, 0);
    return [...p].map(([c, q]) => [at.get(c), q]);
  });
  return Object.freeze({ succ, head: cells });
};

/** The plain cell graph in the same shape (every lane edge a state, every turn allowed). */
export const cellGraph = (net) => {
  const N = net.W * net.H;
  const cells = [...Array(N).keys()].filter((c) => net.road[c]);
  const at = new Map(cells.map((c, i) => [c, i]));
  const succ = cells.map((c) => {
    const outs = [...net.outList.subarray(net.outStart[c], net.outStart[c + 1])];
    return outs.map((d) => [at.get(d), 1 / outs.length]);
  });
  return Object.freeze({ succ, head: cells });
};

/** Shortest directed cycle length of a graph { succ } (Infinity if acyclic). BFS with pruning. */
export const girthOf = ({ succ }) => {
  const n = succ.length;
  const dist = new Int32Array(n).fill(-1);
  const queue = new Int32Array(n);
  let best = Infinity;
  for (let s = 0; s < n; s++) {
    const seen = [s];
    dist[s] = 0;
    let [head, tail] = [0, 0];
    queue[tail++] = s;
    while (head < tail) {
      const u = queue[head++];
      if (dist[u] + 1 >= best) break;
      for (const [v] of succ[u]) {
        if (v === s) { best = Math.min(best, dist[u] + 1); break; }
        if (dist[v] < 0) { dist[v] = dist[u] + 1; seen.push(v); queue[tail++] = v; }
      }
    }
    seen.forEach((v) => { dist[v] = -1; });
  }
  return best;
};

/** Simple cycles of a graph { succ, head } (cells distinct), up to maxLen, each counted once (rooted at its least
 * state). Returns { byLength: Map(len → Σπ), count, shortest: [{ cells, pi }], complete }. */
export const cycleCensus = ({ succ, head }, { maxLen = 24, budget = 2e6, keep = 12 } = {}) => {
  const byLength = new Map();
  const found = [];
  let work = 0, count = 0;
  const onPath = new Uint8Array(succ.length);
  const cellUsed = new Set();
  const path = [];
  const dfs = (root, u, pi) => {
    if (++work > budget) return;
    for (const [v, p] of succ[u]) {
      if (v === root) {
        count++;
        byLength.set(path.length, (byLength.get(path.length) ?? 0) + pi * p);
        found.push({ cells: path.map((s) => head[s]), pi: pi * p });
        continue;
      }
      if (v < root || onPath[v] || cellUsed.has(head[v]) || path.length >= maxLen) continue;
      onPath[v] = 1; cellUsed.add(head[v]); path.push(v);
      dfs(root, v, pi * p);
      onPath[v] = 0; cellUsed.delete(head[v]); path.pop();
    }
  };
  for (let r = 0; r < succ.length && work <= budget; r++) {
    onPath[r] = 1; cellUsed.add(head[r]); path.push(r);
    dfs(r, r, 1);
    onPath[r] = 0; cellUsed.delete(head[r]); path.pop();
  }
  found.sort((x, y) => x.cells.length - y.cells.length || y.pi - x.pi);
  return { byLength, count, shortest: found.slice(0, keep), complete: work <= budget };
};

/** Mean-field index Σ_{|C| ≤ maxLen} ρ^|C| π(C) from a census. */
export const cycleRisk = (census, rho) => [...census.byLength].reduce((a, [len, pi]) => a + pi * rho ** len, 0);

/** λ_max of the turning matrix by power iteration on the left (mass flow). */
export const spectralRadius = ({ succ }, iters = 400) => {
  let x = new Float64Array(succ.length).fill(1 / succ.length);
  let lambda = 0;
  for (let t = 0; t < iters; t++) {
    const y = new Float64Array(succ.length);
    succ.forEach((out, i) => out.forEach(([j, p]) => { y[j] += x[i] * p; }));
    const norm = y.reduce((a, b) => a + b, 0);
    if (norm === 0) return 0;
    lambda = norm / x.reduce((a, b) => a + b, 0);
    x = y.map((v) => v / norm);
  }
  return lambda;
};

/** Upper bound on the long-run exit rate (cars per full step): a max-flow from entries to
 * exits where each cell's capacity is the most cars it can admit per full step. Every cell
 * admits at most one car per half-step (2); under CLASSIC a cell that no car can spawn into
 * admits at most one per two half-steps (1). Unit-augmenting Edmonds–Karp on the split graph. */
export const throughputBound = (net, rule) => {
  const N = net.W * net.H;
  const [S, T] = [2 * N, 2 * N + 1];
  const spawn = spawnCells(net);
  const cap = new Map(); // "u,v" → residual capacity
  const adj = Array.from({ length: 2 * N + 2 }, () => []);
  const arc = (u, v, c) => {
    if (!cap.has(`${u},${v}`)) { adj[u].push(v); adj[v].push(u); if (!cap.has(`${v},${u}`)) cap.set(`${v},${u}`, 0); cap.set(`${u},${v}`, 0); }
    cap.set(`${u},${v}`, cap.get(`${u},${v}`) + c);
  };
  const BIG = 1e9;
  for (let c = 0; c < N; c++) {
    if (!net.road[c]) continue;
    arc(2 * c, 2 * c + 1, rule === CLASSIC && !spawn.has(c) ? 1 : 2);
    for (let i = net.outStart[c]; i < net.outStart[c + 1]; i++) arc(2 * c + 1, 2 * net.outList[i], BIG);
    if (spawn.has(c)) arc(S, 2 * c, BIG);
    if (net.exit[c]) arc(2 * c + 1, T, BIG);
  }
  let flow = 0;
  for (;;) {
    const from = new Map([[S, -1]]);
    const queue = [S];
    for (let h = 0; h < queue.length && !from.has(T); h++)
      for (const v of adj[queue[h]]) if (!from.has(v) && cap.get(`${queue[h]},${v}`) > 0) { from.set(v, queue[h]); queue.push(v); }
    if (!from.has(T)) return flow;
    let push = BIG;
    for (let v = T; v !== S; v = from.get(v)) push = Math.min(push, cap.get(`${from.get(v)},${v}`));
    for (let v = T; v !== S; v = from.get(v)) {
      const u = from.get(v);
      cap.set(`${u},${v}`, cap.get(`${u},${v}`) - push);
      cap.set(`${v},${u}`, cap.get(`${v},${u}`) + push);
    }
    flow += push;
  }
};

/** Axis word (0 horizontal, 1 vertical) of n cells along a straight street at bearing θ
 * (radians from east), as the grid traversal rasterizes it: a Sturmian cutting sequence. */
export const cuttingWord = (theta, n, start = [0.5, 0.31]) => {
  const end = [start[0] + Math.cos(theta) * n * 2, start[1] + Math.sin(theta) * n * 2];
  const cells = traverse(start, end).slice(0, n + 1);
  return cells.slice(1).map(([x], i) => (x !== cells[i][0] ? 0 : 1));
};

/** Free speed under pure two-phase alternation (green = 1) on a straight street at bearing θ:
 * a hop on the other axis than the last takes one half-step, on the same axis two. With
 * α = min(|tan θ|, |cot θ|): 1 + α cells per full step, i.e. 1 / max(|cos θ|, |sin θ|) in
 * cell lengths of straight-line distance. */
export const freeSpeed = (theta) => {
  const [c, s] = [Math.abs(Math.cos(theta)), Math.abs(Math.sin(theta))];
  const alpha = Math.min(c, s) / Math.max(c, s);
  return { cells: 1 + alpha, euclid: 1 / Math.max(c, s), switchRate: (2 * alpha) / (1 + alpha) };
};

/** Half-steps a car needs to traverse a given axis word under two-phase alternation, starting
 * at the half-step whose phase equals the first letter. */
export const traversalTime = (word) => word.reduce((t, a, i) => t + (i === 0 ? 1 : a === word[i - 1] ? 2 : 1), 0);
