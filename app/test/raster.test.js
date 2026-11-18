import { test } from 'node:test';
import assert from 'node:assert/strict';
import { traverse, rasterize, torus, axisOf, girth } from '../src/raster.js';

const outs = (net, c) => [...net.outList.subarray(net.outStart[c], net.outStart[c + 1])];
const cell = (net, x, y) => y * net.W + x;
const allEdges = (net) => [...Array(net.W * net.H).keys()].flatMap((a) => outs(net, a).map((b) => [a, b]));

test('grid traversal is 4-connected and hits both endpoints', () => {
  const path = traverse([0.5, 0.5], [7.2, 3.9]);
  assert.deepEqual(path[0], [0, 0]);
  assert.deepEqual(path.at(-1), [7, 3]);
  path.slice(1).forEach(([x, y], i) => assert.equal(Math.abs(x - path[i][0]) + Math.abs(y - path[i][1]), 1));
});

test('every lane edge is a unit step between road cells', () => {
  const roads = [{ o: 0, c: 4, pts: [-300, 37, 300, 37] }, { o: 1, c: 2, pts: [10, -200, 25, 200] }];
  const net = rasterize(roads, { cols: 12, rows: 8, cell: 7.5, drive: 'R' });
  for (const [a, b] of allEdges(net)) {
    assert.ok(net.road[a] && net.road[b]);
    assert.equal(Math.abs((a % 12) - (b % 12)) + Math.abs(Math.floor(a / 12) - Math.floor(b / 12)), 1);
  }
});

test('a two-way street becomes two opposite lanes on the correct side', () => {
  // centre line along y = 0 (between rows 3 and 4 of an 8-row grid)
  const road = [{ o: 0, c: 4, pts: [-1000, 0, 1000, 0] }];
  const right = rasterize(road, { cols: 10, rows: 8, cell: 7.5, drive: 'R' });
  assert.deepEqual(outs(right, cell(right, 4, 3)), [cell(right, 5, 3)]); // south lane eastbound
  assert.deepEqual(outs(right, cell(right, 5, 4)), [cell(right, 4, 4)]); // north lane westbound
  const left = rasterize(road, { cols: 10, rows: 8, cell: 7.5, drive: 'L' });
  assert.deepEqual(outs(left, cell(left, 4, 3)), [cell(left, 3, 3)]);
  assert.deepEqual(outs(left, cell(left, 5, 4)), [cell(left, 6, 4)]);
  assert.ok(right.exit[cell(right, 9, 3)] && right.entries.includes(cell(right, 0, 3)));
});

test('a one-way street is a single lane in its direction (oneway=-1 reverses)', () => {
  const fwd = rasterize([{ o: 1, c: 4, pts: [-1000, 37, 1000, 37] }], { cols: 10, rows: 8, cell: 7.5, drive: 'R' });
  const rev = rasterize([{ o: -1, c: 4, pts: [-1000, 37, 1000, 37] }], { cols: 10, rows: 8, cell: 7.5, drive: 'R' });
  assert.equal(fwd.road.reduce((a, b) => a + b, 0), 10);
  assert.deepEqual(outs(fwd, cell(fwd, 2, 4)), [cell(fwd, 3, 4)]);
  assert.deepEqual(outs(rev, cell(rev, 3, 4)), [cell(rev, 2, 4)]);
});

test('dead ends inside the window get a turn-around edge', () => {
  const net = rasterize([{ o: 0, c: 4, pts: [-1000, 0, 0, 0] }], { cols: 10, rows: 8, cell: 7.5, drive: 'R' });
  for (let c = 0; c < net.W * net.H; c++)
    if (net.road[c] && !net.exit[c]) assert.ok(net.outStart[c + 1] > net.outStart[c], `cell ${c} has no exit`);
});

test('torus: east and north out-edges with wrap; axes', () => {
  const net = torus(4, 3);
  assert.deepEqual(outs(net, cell(net, 3, 2)).sort((a, b) => a - b), [cell(net, 0, 2), cell(net, 3, 0)].sort((a, b) => a - b));
  assert.equal(axisOf(net, cell(net, 3, 2), cell(net, 0, 2)), 0);
  assert.equal(axisOf(net, cell(net, 3, 2), cell(net, 3, 0)), 1);
});

test('directed girth of the BML torus is min(W, H) — the G1 jam threshold', () => {
  for (const [w, h] of [[2, 2], [3, 5], [7, 4], [6, 6], [1, 5]]) assert.equal(girth(torus(w, h)), Math.min(w, h));
});

test('real presets: no head-on 2-cycles, every lane edge a unit step', async () => {
  const { readFileSync } = await import('node:fs');
  const { PLACES, WINDOW } = await import('../src/presets.js');
  const presets = JSON.parse(readFileSync(new URL('../data/presets.json', import.meta.url)));
  for (const p of presets.places) {
    const net = rasterize(p.roads, { ...WINDOW, drive: PLACES.find((q) => q.id === p.id).drive });
    const set = new Set(allEdges(net).map(([a, b]) => `${a},${b}`));
    for (const [a, b] of allEdges(net)) assert.ok(!set.has(`${b},${a}`), `${p.id}: 2-cycle ${a}↔${b}`);
    assert.ok(girth(net) >= 3, p.id);
  }
});
