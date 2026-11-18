// Pixel renderer: arcade-maze walls from the lane raster, cars as ghost-coloured sprites.
// Model y points north; screen rows run south, so row = H − 1 − y.
import { isStalled, greenAxis } from './sim.js';

export const COLORS = Object.freeze({
  void: '#050510', block: '#0b0b2a', wall: '#2b3bff', pellet: '#ffb8ae', cool: '#4de3ff',
  pac: '#ffd23f', frightened: '#2a2aff', white: '#f4f2ff', hazard: '#ff8c1a', text: '#e8e6ff',
  ghosts: ['#ff3b3b', '#ffb8ff', '#4de3ff', '#ffb852'],
});

/** Pixels per cell: 4 on city maps; as large as fits on the lab torus. */
export const cellPx = (net, w, h) => (net.wrap ? Math.max(2, Math.floor(Math.min(w / net.W, h / net.H))) : 4);

export const drawMaze = (net, px) => {
  const cv = new OffscreenCanvas(net.W * px, net.H * px);
  const g = cv.getContext('2d');
  g.fillStyle = COLORS.void; g.fillRect(0, 0, cv.width, cv.height);
  if (net.wrap) { // the torus is all road: a faint lattice instead of walls
    g.fillStyle = '#16163a';
    for (let y = 0; y < net.H; y++) for (let x = 0; x < net.W; x++) g.fillRect(x * px + (px >> 1), y * px + (px >> 1), 1, 1);
    return cv;
  }
  const road = (x, y) => x >= 0 && y >= 0 && x < net.W && y < net.H && net.road[y * net.W + x];
  for (let y = 0; y < net.H; y++)
    for (let x = 0; x < net.W; x++) {
      if (road(x, y)) continue;
      const [sx, sy] = [x * px, (net.H - 1 - y) * px];
      g.fillStyle = COLORS.block; g.fillRect(sx, sy, px, px);
      g.fillStyle = COLORS.wall;
      if (road(x - 1, y)) g.fillRect(sx, sy, 1, px);
      if (road(x + 1, y)) g.fillRect(sx + px - 1, sy, 1, px);
      if (road(x, y + 1)) g.fillRect(sx, sy, px, 1);
      if (road(x, y - 1)) g.fillRect(sx, sy + px - 1, px, 1);
    }
  return cv;
};

/** One frame. view = { net, px, maze, sim, frozen, opts, fx, now, lab? } */
export const drawFrame = (g, view) => {
  const { net, px, maze, sim, frozen, opts, fx, now, lab } = view;
  g.drawImage(maze, 0, 0);
  const H = net.H, W = net.W;
  const blink = Math.floor(now / 160) % 2 === 0;
  const scr = (c) => [(c % W) * px, (H - 1 - Math.floor(c / W)) * px];

  if (!net.wrap && opts.green > 1) { // junction pellets show which axis has green
    g.fillStyle = greenAxis(sim.t, opts.green) ? COLORS.cool : COLORS.pellet;
    for (let c = 0; c < W * H; c++) if (net.junction[c] && sim.occ[c] < 0) { const [x, y] = scr(c); g.fillRect(x + 1, y + 1, 1, 1); }
  }

  const body = Math.max(2, px - 1);
  for (let k = 0; k < sim.pos.length; k++) {
    const c = sim.pos[k];
    if (c < 0) continue;
    const [x, y] = scr(c);
    const f = frozen[k];
    const color = lab ? (sim.species[k] === 1 ? COLORS.cool : COLORS.ghosts[1])
      : isStalled(sim, k) ? (blink ? COLORS.hazard : '#5a2a00')
      : f === 2 ? (blink ? COLORS.frightened : COLORS.white)
      : f === 1 ? COLORS.frightened
      : COLORS.ghosts[k % 4];
    g.globalAlpha = lab || f || sim.last[k] >= sim.t - 2 ? 1 : 0.55;
    g.fillStyle = color; g.fillRect(x, y, body, body);
    const n = sim.next[k];
    if (n >= 0 && n !== c && px >= 4) { // headlight on the side it will move to
      const dx = Math.sign(((n % W) - (c % W) + W + W / 2) % W - W / 2);
      const dy = -Math.sign(((Math.floor(n / W) - Math.floor(c / W) + H + H / 2) % H) - H / 2);
      g.fillStyle = COLORS.white;
      g.fillRect(x + (body >> 1) + dx * (body >> 1), y + (body >> 1) + dy * (body >> 1), 1, 1);
    }
  }
  g.globalAlpha = 1;

  g.font = '8px "Press Start 2P", monospace';
  g.textAlign = 'center';
  for (const e of fx) {
    const age = (now - e.at) / 900;
    if (age > 1) continue;
    const [x, y] = scr(e.cell);
    g.fillStyle = e.color;
    g.fillText(e.text, Math.min(Math.max(x, 24), W * px - 24), Math.max(10, y - age * 14));
  }
};

/** Fundamental diagram (density ρ vs flow J): sweep points plus the live point. */
export const drawDiagram = (g, { points, live, w, h }) => {
  g.fillStyle = COLORS.void; g.fillRect(0, 0, w, h);
  const [l, b, r, t] = [22, h - 14, w - 16, 12];
  const jMax = Math.max(0.2, ...points.map((p) => p.j), live?.j ?? 0);
  const X = (rho) => l + (rho / 0.8) * (r - l);
  const Y = (j) => b - (j / jMax) * (b - t);
  g.fillStyle = '#20204a';
  for (let i = 0; i <= 4; i++) g.fillRect(X(i * 0.2), t, 1, b - t);
  g.fillStyle = COLORS.wall; g.fillRect(l, b, r - l, 1); g.fillRect(l, t, 1, b - t);
  g.fillStyle = COLORS.text; g.font = '8px "Press Start 2P", monospace'; g.textAlign = 'left';
  g.fillText('J', 4, t + 6); g.textAlign = 'right'; g.fillText('ρ', w - 2, b - 4);
  g.textAlign = 'center';
  [0, 0.4, 0.8].forEach((v) => g.fillText(String(v), X(v), h - 2));
  g.fillStyle = COLORS.pac;
  points.forEach((p) => g.fillRect(Math.round(X(p.rho)) - 1, Math.round(Y(p.j)) - 1, 3, 3));
  if (live) { g.fillStyle = COLORS.ghosts[0]; g.fillRect(Math.round(X(live.rho)) - 2, Math.round(Y(live.j)) - 2, 5, 5); }
};
