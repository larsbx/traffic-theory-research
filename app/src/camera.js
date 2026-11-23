// Pinhole camera over the ground plane z = 0 (world units = cells, y north, z up).
// pitch: angle below the horizon (π/2 = straight down); yaw: heading, 0 = looking north.
// No roll, so `right` is horizontal and every screen row meets the ground at one depth:
// a row of ground pixels is an affine image of a world segment (Mode 7, generalised).

const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];

/** A camera looking at `target` (default: the map centre). zoom = 1 frames the whole W×H map
 * with a `margin` (fraction of the screen); zoom > 1 moves in. */
export const camera = ({ W, H, width, height, pitch, yaw, fov = Math.PI / 4, zoom = 1, margin = 0.04, target }) => {
  const at = (d) => cameraAt({ W, H, width, height, pitch, yaw, fov, d, target: [W / 2, H / 2, 0] });
  const inside = (cam) => [[0, 0], [W, 0], [0, H], [W, H]].every((c) => {
    const [sx, sy, z] = project(cam, [...c, 0]);
    return z > 0 && sx >= width * margin && sx <= width * (1 - margin) && sy >= height * margin && sy <= height * (1 - margin);
  });
  let [lo, hi] = [1e-3, Math.hypot(W, H) * 50];
  for (let i = 0; i < 48; i++) { const mid = (lo + hi) / 2; if (inside(at(mid))) hi = mid; else lo = mid; }
  return cameraAt({ W, H, width, height, pitch, yaw, fov, d: hi / zoom, target: target ?? [W / 2, H / 2, 0] });
};

const cameraAt = ({ W, H, width, height, pitch, yaw, fov, d, target }) => {
  const forward = [Math.sin(yaw) * Math.cos(pitch), Math.cos(yaw) * Math.cos(pitch), -Math.sin(pitch)];
  const right = [Math.cos(yaw), -Math.sin(yaw), 0];
  const up = [ // right × forward
    right[1] * forward[2] - right[2] * forward[1],
    right[2] * forward[0] - right[0] * forward[2],
    right[0] * forward[1] - right[1] * forward[0],
  ];
  const f = height / 2 / Math.tan(fov / 2);
  const eye = target.map((t, i) => t - forward[i] * d);
  return Object.freeze({ W, H, width, height, forward, right, up, f, eye, cx: width / 2, cy: height / 2 });
};

/** World point → [sx, sy, depth]; depth ≤ 0 means behind the camera. */
export const project = (cam, [x, y, z]) => {
  const r = [x - cam.eye[0], y - cam.eye[1], z - cam.eye[2]];
  const zc = dot(r, cam.forward);
  return [cam.cx + (cam.f * dot(r, cam.right)) / zc, cam.cy - (cam.f * dot(r, cam.up)) / zc, zc];
};

/** Where the ray through screen point (sx, sy) meets the ground, or null (sky). */
export const unproject = (cam, sx, sy) => {
  const [u, v] = [(sx - cam.cx) / cam.f, (cam.cy - sy) / cam.f];
  const dir = [0, 1, 2].map((i) => cam.forward[i] + u * cam.right[i] + v * cam.up[i]);
  if (dir[2] >= -1e-9) return null;
  const t = -cam.eye[2] / dir[2];
  return [cam.eye[0] + t * dir[0], cam.eye[1] + t * dir[1], t * Math.hypot(...dir)];
};

/** For each screen row: ground point at the left and right edges plus distance, or null. */
export const groundRows = (cam) =>
  Array.from({ length: cam.height }, (_, sy) => {
    const [a, b] = [unproject(cam, 0, sy + 0.5), unproject(cam, cam.width, sy + 0.5)];
    return a && b ? { x0: a[0], y0: a[1], x1: b[0], y1: b[1], dist: a[2] } : null;
  });
