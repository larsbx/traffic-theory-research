// Pixel renderer: the lane raster becomes an arcade-maze texture on a ground plane seen in
// perspective (camera.js); cars are lit 3D shapes. In the texture, row = H − 1 − y.
import { isStalled, greenAxis } from './sim.js';
import { project, groundRows } from './camera.js';
import { edgeHeading } from './raster.js';

export const COLORS = Object.freeze({
  void: '#050510', block: '#0b0b2a', wall: '#2b3bff', pellet: '#ffb8ae', cool: '#4de3ff',
  pac: '#ffd23f', frightened: '#2a2aff', white: '#f4f2ff', hazard: '#ff8c1a', text: '#e8e6ff',
  ghosts: ['#ff3b3b', '#ffb8ff', '#4de3ff', '#ffb852'],
});

/** Straight streets: each lane polyline stroked as a corridor, wall-blue edge, black road. */
const drawLanes = (g, net, px) => {
  const path = (ln) => {
    g.beginPath();
    for (let i = 0; i < ln.length; i += 2) {
      const [x, y] = [ln[i] * px, (net.H - ln[i + 1]) * px];
      if (i) g.lineTo(x, y); else g.moveTo(x, y);
    }
  };
  g.lineCap = 'round'; g.lineJoin = 'round';
  g.fillStyle = COLORS.block; g.fillRect(0, 0, net.W * px, net.H * px);
  g.strokeStyle = COLORS.wall; g.lineWidth = px + 2;
  net.lanes.forEach((ln) => { path(ln); g.stroke(); });
  g.strokeStyle = COLORS.void; g.lineWidth = px;
  net.lanes.forEach((ln) => { path(ln); g.stroke(); });
};

export const drawMaze = (net, px) => {
  const cv = new OffscreenCanvas(net.W * px, net.H * px);
  const g = cv.getContext('2d');
  g.fillStyle = COLORS.void; g.fillRect(0, 0, cv.width, cv.height);
  if (net.lanes?.length) { drawLanes(g, net, px); return cv; }
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

// ---------- perspective view ----------

export const TEX = 6; // texture pixels per cell

/** The flat maze as a texture: { data: Uint32Array (ABGR), w, h }. */
export const texture = (net) => {
  const cv = drawMaze(net, TEX);
  const img = cv.getContext('2d').getImageData(0, 0, cv.width, cv.height);
  return { data: new Uint32Array(img.data.buffer), w: cv.width, h: cv.height };
};

const rgb = (hex) => [1, 3, 5].map((i) => parseInt(hex.slice(i, i + 2), 16));
const abgr = ([r, g, b]) => (255 << 24 | b << 16 | g << 8 | r) >>> 0;
const SKY_TOP = rgb('#02020a'), SKY_LOW = rgb('#1a0f3a'), FOG = rgb('#0d0a26'), OFF = rgb('#03030c');

/** Ground plane + sky for a camera, as ImageData (recompute only when the camera moves). */
export const drawGround = (cam, tex, net) => {
  const img = new ImageData(cam.width, cam.height);
  const out = new Uint32Array(img.data.buffer);
  const rows = groundRows(cam);
  const horizon = rows.findIndex(Boolean);
  const near = Math.min(...rows.filter(Boolean).map((r) => r.dist));
  const far = Math.max(...rows.filter(Boolean).map((r) => r.dist));
  const off = abgr(OFF);
  rows.forEach((row, sy) => {
    const base = sy * cam.width;
    if (!row) { // sky: a dusk gradient down to the horizon
      const k = horizon > 0 ? sy / horizon : 1;
      out.fill(abgr(SKY_TOP.map((c, i) => Math.round(c + (SKY_LOW[i] - c) * k))), base, base + cam.width);
      return;
    }
    const fog = Math.min(0.85, Math.max(0, (row.dist - near) / (far - near + 1e-9)) ** 1.6 * 0.85);
    const [dx, dy] = [(row.x1 - row.x0) / cam.width, (row.y1 - row.y0) / cam.width];
    for (let i = 0; i < cam.width; i++) {
      const [x, y] = [row.x0 + dx * (i + 0.5), row.y0 + dy * (i + 0.5)];
      const tx = Math.floor(x * TEX), ty = Math.floor((net.H - y) * TEX);
      const t = tx >= 0 && ty >= 0 && tx < tex.w && ty < tex.h ? tex.data[ty * tex.w + tx] : off;
      const r = t & 255, g = (t >>> 8) & 255, b = (t >>> 16) & 255;
      out[base + i] = (255 << 24 | (b + (FOG[2] - b) * fog) << 16 | (g + (FOG[1] - g) * fog) << 8 | (r + (FOG[0] - r) * fog)) >>> 0;
    }
  });
  return img;
};

const shade = (hex, k) => `rgb(${rgb(hex).map((c) => Math.min(255, Math.round(c * k))).join(',')})`;
const LIGHT = (() => { const l = [-0.45, -0.6, 0.66]; const n = Math.hypot(...l); return l.map((c) => c / n); })();

/** A box: footprint centre (x, y), heading (hx, hy), length L, width w, from z0 to z1. */
const box = (g, cam, [x, y], [hx, hy], L, w, z0, z1, color, alpha) => {
  const [px, py] = [-hy, hx];
  const ring = [[1, 1], [-1, 1], [-1, -1], [1, -1]].map(([a, b]) => [x + (hx * a * L) / 2 + (px * b * w) / 2, y + (hy * a * L) / 2 + (py * b * w) / 2]);
  const bottom = ring.map(([a, b]) => project(cam, [a, b, z0]));
  const top = ring.map(([a, b]) => project(cam, [a, b, z1]));
  if (top.some((p) => p[2] <= 0.1)) return;
  const faces = ring.map((_, i) => {
    const j = (i + 1) % 4;
    const m = [(ring[i][0] + ring[j][0]) / 2 - x, (ring[i][1] + ring[j][1]) / 2 - y]; // outward normal
    const len = Math.hypot(...m) || 1;
    const nrm = [m[0] / len, m[1] / len, 0];
    const mid = [(ring[i][0] + ring[j][0]) / 2, (ring[i][1] + ring[j][1]) / 2, (z0 + z1) / 2];
    const toEye = [cam.eye[0] - mid[0], cam.eye[1] - mid[1], cam.eye[2] - mid[2]];
    return { pts: [bottom[i], bottom[j], top[j], top[i]], nrm, show: nrm[0] * toEye[0] + nrm[1] * toEye[1] > 0 };
  });
  g.globalAlpha = alpha;
  for (const f of faces.filter((f) => f.show)) {
    const lit = 0.45 + 0.4 * Math.max(0, f.nrm[0] * LIGHT[0] + f.nrm[1] * LIGHT[1]);
    g.fillStyle = shade(color, lit);
    g.beginPath(); f.pts.forEach(([sx, sy], k) => (k ? g.lineTo(sx, sy) : g.moveTo(sx, sy))); g.fill();
  }
  if (cam.eye[2] > z1) {
    g.fillStyle = shade(color, 1.05);
    g.beginPath(); top.forEach(([sx, sy], k) => (k ? g.lineTo(sx, sy) : g.moveTo(sx, sy))); g.fill();
  }
  g.globalAlpha = 1;
};

/** Display length of a car at `cell` between its neighbours `prev` and `next` (−1: none). Two cars
 * in adjacent cells sit gap = |disp(a) − disp(b)| apart; each takes at most 0.92 × its smaller
 * neighbouring gap, so half-lengths sum to < gap and queued cars never overlap. */
export const carLength = (net, prev, cell, next) => {
  const gap = (n) => (n >= 0 && n !== cell && !net.wrap
    ? Math.hypot(net.disp[2 * n] - net.disp[2 * cell], net.disp[2 * n + 1] - net.disp[2 * cell + 1]) : 1);
  return Math.min(0.96, 0.92 * Math.min(gap(prev), gap(next)));
};

/** Unit heading of car k: its lane's true street heading (so cars face along straight streets). */
const headingOf = (net, sim, k) => {
  const [a, b] = sim.next[k] >= 0 && sim.next[k] !== sim.pos[k] ? [sim.pos[k], sim.next[k]] : sim.prev[k] >= 0 ? [sim.prev[k], sim.pos[k]] : [-1, -1];
  const h = a >= 0 ? edgeHeading(net, a, b) : sim.species[k] === 2 ? Math.PI / 2 : 0;
  return Number.isFinite(h) ? [Math.cos(h), Math.sin(h)] : [1, 0];
};

/** One frame. view = { net, ground (ImageData), cam, sim, frozen, opts, fx, now, lab? } */
export const drawFrame = (g, view) => {
  const { net, ground, cam, sim, frozen, opts, fx, now, lab } = view;
  g.putImageData(ground, 0, 0);
  const W = net.W;
  const blink = Math.floor(now / 160) % 2 === 0;
  const centre = (c, z = 0) => [net.disp[2 * c], net.disp[2 * c + 1], z]; // the cell's point on its street

  if (!net.wrap && opts.green > 1) { // junction lamps show which axis has green
    g.fillStyle = greenAxis(sim.t, opts.green) ? COLORS.cool : COLORS.pellet;
    for (let c = 0; c < W * net.H; c++)
      if (net.junction[c] && sim.occ[c] < 0) {
        const [sx, sy, d] = project(cam, centre(c));
        if (d > 0) g.fillRect(Math.round(sx) - 1, Math.round(sy) - 1, 2, 2);
      }
  }

  const cars = [];
  for (let k = 0; k < sim.pos.length; k++) if (sim.pos[k] >= 0) cars.push([k, project(cam, centre(sim.pos[k]))[2]]);
  cars.sort((a, b) => b[1] - a[1]); // painter's order: far to near
  for (const [k] of cars) {
    const f = frozen[k];
    const color = lab ? (sim.species[k] === 1 ? COLORS.cool : COLORS.ghosts[1])
      : isStalled(sim, k) ? (blink ? COLORS.hazard : '#7a3a00')
      : f === 2 ? (blink ? COLORS.frightened : COLORS.white)
      : f === 1 ? COLORS.frightened
      : COLORS.ghosts[k % 4];
    const alpha = lab || f || sim.last[k] >= sim.t - 2 ? 1 : 0.7;
    const [cx, cy] = centre(sim.pos[k]);
    const [hx, hy] = headingOf(net, sim, k);
    const len = carLength(net, sim.prev[k], sim.pos[k], sim.next[k]); // fits diagonal spacing
    box(g, cam, [cx, cy], [hx, hy], len, 0.7, 0, 0.36, color, alpha); // body
    box(g, cam, [cx - hx * 0.1 * len, cy - hy * 0.1 * len], [hx, hy], 0.52 * len, 0.56, 0.36, 0.62, color, alpha); // cabin, set back
    const [lx, ly] = project(cam, [cx + hx * 0.5 * len, cy + hy * 0.5 * len, 0.22]); // headlight
    g.fillStyle = COLORS.white; g.fillRect(Math.round(lx) - 1, Math.round(ly) - 1, 2, 2);
  }

  g.font = '8px "Press Start 2P", monospace';
  g.textAlign = 'center';
  for (const e of fx) {
    const age = (now - e.at) / 900;
    if (age > 1) continue;
    const [sx, sy, d] = project(cam, centre(e.cell, 1.4 + age));
    if (d <= 0) continue;
    g.fillStyle = e.color;
    g.fillText(e.text, Math.min(Math.max(sx, 40), cam.width - 40), Math.max(10, sy));
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
