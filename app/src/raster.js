// Street centre-lines → a directed lane graph on a W×H cell grid.
// Cell c = y·W + x with y increasing northwards. Every edge is a unit step, so each move
// is horizontal (axis 0) or vertical (axis 1): the two BML species and the two signal phases.

/** Cells crossed by the segment p→q (grid units), in order — Amanatides–Woo traversal. */
export const traverse = ([x0, y0], [x1, y1]) => {
  let [x, y] = [Math.floor(x0), Math.floor(y0)];
  const [xe, ye] = [Math.floor(x1), Math.floor(y1)];
  const [dx, dy] = [x1 - x0, y1 - y0];
  const [sx, sy] = [Math.sign(dx), Math.sign(dy)];
  const tdx = sx ? Math.abs(1 / dx) : Infinity;
  const tdy = sy ? Math.abs(1 / dy) : Infinity;
  let tx = sx ? (sx > 0 ? x + 1 - x0 : x0 - x) * tdx : Infinity;
  let ty = sy ? (sy > 0 ? y + 1 - y0 : y0 - y) * tdy : Infinity;
  const out = [[x, y]];
  for (let n = Math.abs(xe - x) + Math.abs(ye - y); n > 0; n--) {
    if (tx < ty) { x += sx; tx += tdx; } else { y += sy; ty += tdy; }
    out.push([x, y]);
  }
  return out;
};

const pairs = (pts) => Array.from({ length: pts.length / 2 }, (_, i) => [pts[2 * i], pts[2 * i + 1]]);

/** Offset a polyline sideways by d (positive = right of travel), mitre joins clamped.
 * Each segment's normal is scaled by |cos θ| + |sin θ|: a 4-connected staircase at angle θ is
 * that many cells thick, so opposite lanes of a diagonal street stay disjoint. */
const offset = (line, d) => {
  const normals = line.slice(1).map(([x, y], i) => {
    const [ux, uy] = [x - line[i][0], y - line[i][1]];
    const len = Math.hypot(ux, uy) || 1;
    const band = (Math.abs(ux) + Math.abs(uy)) / len;
    return [(uy / len) * band, (-ux / len) * band];
  });
  return line.map(([x, y], i) => {
    const [a, b] = [normals[Math.max(0, i - 1)], normals[Math.min(normals.length - 1, i)]];
    const [mx, my] = [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2];
    const k = Math.max((mx * a[0] + my * a[1]) / (Math.hypot(...a) ** 2 || 1), 0.5); // mitre, clamped
    return [x + (d * mx) / k, y + (d * my) / k];
  });
};

/** Extend both ends by e so lanes reach across junction centre-lines. */
const extend = (line, e) => {
  const tip = (p, q) => {
    const len = Math.hypot(p[0] - q[0], p[1] - q[1]) || 1;
    return [p[0] + ((p[0] - q[0]) * e) / len, p[1] + ((p[1] - q[1]) * e) / len];
  };
  return [tip(line[0], line[1]), ...line, tip(line.at(-1), line.at(-2))];
};

/** Lanes of one road as metre polylines in travel order. */
const lanes = ({ o, pts }, cell, drive) => {
  const line = pairs(pts).map(([x, y]) => [x / 10, y / 10]);
  if (line.length < 2) return [];
  const fwd = o === -1 ? [...line].reverse() : line;
  if (o !== 0) return [fwd];
  const side = (drive === 'L' ? -1 : 1) * cell / 2;
  return [offset(fwd, side), offset([...fwd].reverse(), side)];
};

/** Compressed adjacency from an edge set; also the reverse lists and each edge's lane heading
 * (radians, the street's true direction — a staircase step still has its street's heading). */
const csr = (n, edges) => {
  const build = (key, val, Typed = Int32Array) => {
    const start = new Int32Array(n + 1);
    edges.forEach((e) => start[key(e) + 1]++);
    for (let i = 0; i < n; i++) start[i + 1] += start[i];
    const fill = start.slice(0, n);
    const list = new Typed(edges.length);
    edges.forEach((e) => { list[fill[key(e)]++] = val(e); });
    return [start, list];
  };
  const [outStart, outList] = build(([a]) => a, ([, b]) => b);
  const [, outHeading] = build(([a]) => a, ([, , , h]) => h, Float32Array);
  const [inStart, inList] = build(([, b]) => b, ([a]) => a);
  return { outStart, outList, outHeading, inStart, inList };
};

export const network = ({ W, H, road, edges, exit = new Uint8Array(W * H), entries = [], drive = 'R', wrap = false }) => {
  const adj = csr(W * H, edges);
  // A junction is entered along both axes: the cells a traffic signal governs.
  const junction = Uint8Array.from({ length: W * H }, (_, c) => {
    const axes = new Set([...adj.inList.subarray(adj.inStart[c], adj.inStart[c + 1])].map((a) => (Math.floor(a / W) === Math.floor(c / W) ? 0 : 1)));
    return axes.size > 1 ? 1 : 0;
  });
  return Object.freeze({ W, H, road, exit, junction, entries: Int32Array.from(entries), drive, wrap, roadCells: road.reduce((a, b) => a + b, 0), ...adj });
};

/** Heading of the edge a→b (NaN if absent). */
export const edgeHeading = (net, a, b) => {
  for (let i = net.outStart[a]; i < net.outStart[a + 1]; i++) if (net.outList[i] === b) return net.outHeading[i];
  return NaN;
};

/** 0 = horizontal move, 1 = vertical move. */
export const axisOf = (net, a, b) => (Math.floor(a / net.W) === Math.floor(b / net.W) ? 0 : 1);

/** Is cell c entered along both axes (by the current edge set)? */
const junctions = (edges, W) => {
  const axes = new Map();
  for (const [a, b] of edges.values()) {
    const ax = Math.floor(a / W) === Math.floor(b / W) ? 1 : 2;
    axes.set(b, (axes.get(b) ?? 0) | ax);
  }
  return (c) => axes.get(c) === 3;
};

/** Shortest directed cycles of ≤ RING cells through some non-junction cell are artefacts of
 * lanes crossing at shallow angles: at 7.5 m a real block has a perimeter of ≳ 16 cells, and a
 * real two-way crossing box (4 junction cells) is kept. Each such ring is a ready-made jam core,
 * so drop its weakest edge — extension first, then turn-around, then the minor road's. */
const RING = 12;
const pruneMicroRings = (edges, W) => {
  const ringThrough = (adj, a, b) => { // shortest path b ⇝ a (BFS, depth < RING), as a cell list
    const from = new Map([[b, -1]]);
    for (let frontier = [b], d = 1; frontier.length && d < RING; d++) {
      const next = [];
      for (const u of frontier)
        for (const v of adj.get(u) ?? []) {
          if (from.has(v)) continue;
          from.set(v, u);
          if (v === a) { const ring = []; for (let x = a; x !== -1; x = from.get(x)) ring.unshift(x); return ring; }
          next.push(v);
        }
      frontier = next;
    }
    return null;
  };
  for (let changed = true; changed;) {
    changed = false;
    const isJ = junctions(edges, W);
    const adj = new Map();
    for (const [a, b] of edges.values()) adj.set(a, [...(adj.get(a) ?? []), b]);
    for (const [a, b] of edges.values()) {
      const path = ringThrough(adj, a, b); // b … a, closed by a → b
      if (!path || path.every(isJ)) continue;
      const ringEdges = path.map((x, i) => edges.get(`${x},${path[(i + 1) % path.length]}`));
      const weakest = ringEdges.reduce((w, e) => (e[2] > w[2] ? e : w));
      edges.delete(`${weakest[0]},${weakest[1]}`);
      changed = true;
      break;
    }
  }
};

export const rasterize = (roads, { cols: W, rows: H, cell, drive = 'R' }) => {
  const inside = ([x, y]) => x >= 0 && y >= 0 && x < W && y < H;
  const id = ([x, y]) => y * W + x;
  const road = new Uint8Array(W * H);
  const exit = new Uint8Array(W * H);
  const entries = new Set();
  const edges = new Map(); // "a,b" → [a, b, rank, heading]; lower rank = stronger provenance
  const addEdge = (a, b, rank, heading) => {
    const old = edges.get(`${a},${b}`);
    if (!old || rank < old[2]) edges.set(`${a},${b}`, [a, b, rank, heading]);
  };

  for (const r of roads)
    for (const lane of lanes(r, cell, drive)) {
      const grid = extend(lane, cell * 0.75).map(([x, y]) => [x / cell + W / 2, y / cell + H / 2]);
      // segment index per cell: the first and last segments are the artificial extensions
      const cells = grid.slice(1).flatMap((q, i) => traverse(grid[i], q).slice(i ? 1 : 0).map((c) => [...c, i]));
      const headings = grid.slice(1).map((q, i) => Math.atan2(q[1] - grid[i][1], q[0] - grid[i][0]));
      const last = grid.length - 2;
      cells.forEach((c, i) => {
        if (!inside(c)) return;
        road[id(c)] = 1;
        const [p, n] = [cells[i - 1], cells[i + 1]];
        if (p && !inside(p)) entries.add(id(c));
        if (n && !inside(n)) exit[id(c)] = 1;
        const ext = n && (n[2] === 0 || n[2] === last);
        if (n && inside(n) && id(n) !== id(c)) addEdge(id(c), id(n), (ext ? 100 : 0) + r.c, headings[n[2]]);
      });
    }

  // Opposing lanes sharing two cells would make a head-on 2-cycle — an immediate permanent
  // jam core. Keep the edge with stronger provenance (real lane over extension, major over minor).
  for (const [key, [a, b, rank]] of [...edges])
    if (a < b && edges.has(`${b},${a}`)) {
      const kept = edges.get(key);
      const back = edges.get(`${b},${a}`)[2];
      if (rank >= back) edges.delete(key);
      if (back >= rank) edges.delete(`${b},${a}`);
      if (back === rank) edges.set(key, kept); // tie: keep one direction, deterministically
    }

  pruneMicroRings(edges, W);

  // Turn-arounds: a dead end that is not a map exit links to a neighbouring lane it does not come from.
  const outDeg = new Int32Array(W * H);
  const preds = new Map();
  for (const [a, b] of edges.values()) { outDeg[a]++; preds.set(b, [...(preds.get(b) ?? []), a]); }
  for (let c = 0; c < W * H; c++) {
    if (!road[c] || exit[c] || outDeg[c]) continue;
    const [x, y] = [c % W, Math.floor(c / W)];
    const nbrs = [[x + 1, y], [x - 1, y], [x, y + 1], [x, y - 1]].filter(inside).map(id)
      .filter((n) => road[n] && !(preds.get(c) ?? []).includes(n));
    const target = nbrs.find((n) => outDeg[n]) ?? nbrs[0];
    if (target === undefined) exit[c] = 1; // isolated stub: treat as a sink
    else edges.set(`${c},${target}`, [c, target, 50, Math.atan2(Math.floor(target / W) - y, (target % W) - x)]);
  }
  pruneMicroRings(edges, W); // a turn-around can close a new ring; any dead end it leaves is a sink
  const hasOut = new Set([...edges.values()].map(([a]) => a));
  for (let c = 0; c < W * H; c++) if (road[c] && !hasOut.has(c)) exit[c] = 1;
  return network({ W, H, road, edges: [...edges.values()], exit, entries: [...entries], drive });
};

/** The BML torus: every cell has an east and a north out-edge (with wrap-around). */
export const torus = (W, H) => {
  const edges = [];
  for (let y = 0; y < H; y++)
    for (let x = 0; x < W; x++) {
      const c = y * W + x;
      // A 1-wide dimension makes the move a self-loop: the cell ahead is the car's own cell.
      edges.push([c, y * W + ((x + 1) % W), 0, 0]);
      edges.push([c, ((y + 1) % H) * W + x, 0, Math.PI / 2]);
    }
  return network({ W, H, road: new Uint8Array(W * H).fill(1), edges, wrap: true });
};

/** Directed girth: length of the shortest directed cycle (Infinity if acyclic). */
export const girth = (net) => {
  const n = net.W * net.H;
  const dist = new Int32Array(n).fill(-1);
  const queue = new Int32Array(n);
  let best = Infinity;
  for (let s = 0; s < n; s++) {
    if (!net.road[s]) continue;
    const seen = [s];
    dist[s] = 0;
    let [head, tail] = [0, 0];
    queue[tail++] = s;
    while (head < tail) {
      const u = queue[head++];
      if (dist[u] + 1 >= best) break;
      for (let i = net.outStart[u]; i < net.outStart[u + 1]; i++) {
        const v = net.outList[i];
        if (v === s) { best = Math.min(best, dist[u] + 1); break; }
        if (dist[v] < 0) { dist[v] = dist[u] + 1; seen.push(v); queue[tail++] = v; }
      }
    }
    seen.forEach((v) => { dist[v] = -1; });
  }
  return best;
};
