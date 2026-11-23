import { test } from 'node:test';
import assert from 'node:assert/strict';
import { camera, project, unproject, groundRows } from '../src/camera.js';

const near = (a, b, eps = 1e-6) => assert.ok(Math.abs(a - b) < eps, `${a} ≉ ${b}`);
const cams = [0.35, 0.8, 1.2, Math.PI / 2 - 1e-3].flatMap((pitch) =>
  [0, 0.7, -2.4, Math.PI].map((yaw) => camera({ W: 96, H: 64, width: 480, height: 300, pitch, yaw })));

test('unproject inverts project on the ground plane', () => {
  for (const cam of cams)
    for (const [x, y] of [[48, 32], [10, 5], [90, 60], [0, 64]]) {
      const [sx, sy, depth] = project(cam, [x, y, 0]);
      assert.ok(depth > 0);
      const g = unproject(cam, sx, sy);
      near(g[0], x); near(g[1], y);
    }
});

test('zoom 1 frames the map tightly: all corners on screen, one touching the margin', () => {
  for (const cam of cams) {
    const [sx, sy] = project(cam, [48, 32, 0]);
    near(sx, 240); near(sy, 150);
    const pts = [[0, 0], [96, 0], [0, 64], [96, 64]].map((c) => project(cam, [...c, 0]));
    assert.ok(pts.every(([x, y, z]) => z > 0 && x >= 480 * 0.04 - 1e-6 && x <= 480 * 0.96 + 1e-6 && y >= 300 * 0.04 - 1e-6 && y <= 300 * 0.96 + 1e-6));
    const slack = Math.min(...pts.flatMap(([x, y]) => [x - 19.2, 460.8 - x, y - 12, 288 - y]));
    assert.ok(slack < 0.5, `slack ${slack}`);
  }
});

test('zoom moves the eye toward the target; a target re-centres the view', () => {
  const base = { W: 96, H: 64, width: 480, height: 300, pitch: 0.8, yaw: 0.3 };
  const [a, b] = [camera(base), camera({ ...base, zoom: 2 })];
  const dist = (c) => Math.hypot(c.eye[0] - 48, c.eye[1] - 32, c.eye[2]);
  near(dist(b), dist(a) / 2, 1e-6);
  const [sx, sy] = project(camera({ ...base, zoom: 3, target: [10, 50, 0] }), [10, 50, 0]);
  near(sx, 240); near(sy, 150);
});

test('ground rows are affine: interior pixels lie on the segment between the row ends', () => {
  const cam = cams[5];
  groundRows(cam).forEach((row, sy) => {
    if (!row) return;
    const g = unproject(cam, 120, sy + 0.5);
    near(g[0], row.x0 + 0.25 * (row.x1 - row.x0), 1e-6);
    near(g[1], row.y0 + 0.25 * (row.y1 - row.y0), 1e-6);
  });
});

test('a low pitch shows sky at the top; straight down shows none; up is up', () => {
  const low = camera({ W: 96, H: 64, width: 480, height: 300, pitch: 0.3, yaw: 0 });
  assert.equal(groundRows(low)[0], null);
  const top = camera({ W: 96, H: 64, width: 480, height: 300, pitch: Math.PI / 2 - 1e-3, yaw: 0 });
  assert.ok(groundRows(top).every(Boolean));
  assert.ok(project(low, [48, 32, 5])[1] < project(low, [48, 32, 0])[1], 'higher points draw higher');
  assert.ok(project(low, [48, 60, 0])[1] < project(low, [48, 10, 0])[1], 'facing north, north is farther up the screen');
});
