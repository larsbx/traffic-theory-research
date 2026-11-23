import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { torus, rasterize, girth } from '../src/raster.js';
import { fromGrid, toGrid, step, halfStep, init, tow, breakDown, isStalled, CLASSIC, TRAIN, EXIT } from '../src/sim.js';
import { certificate, isGridlock, onStreet } from '../src/analysis.js';
import { PLACES, WINDOW } from '../src/presets.js';

const fixture = JSON.parse(readFileSync(new URL('./fixtures/bml-python.json', import.meta.url)));
const presets = JSON.parse(readFileSync(new URL('../data/presets.json', import.meta.url)));
const nets = presets.places.map((p) => [p.id, rasterize(p.roads, { ...WINDOW, drive: PLACES.find((q) => q.id === p.id).drive })]);

test(`torus + fixed species reproduces bml.model.step exactly (${fixture.cases.length} Python orbits)`, () => {
  for (const { W, H, rule, orbit, moves } of fixture.cases) {
    const net = torus(W, H);
    let s = fromGrid(net, orbit[0]);
    orbit.slice(1).forEach((want, i) => {
      const a = halfStep(net, s, { rule });
      s = halfStep(net, a, { rule });
      assert.deepEqual(toGrid(net, s), want, `${W}×${H} ${rule} step ${i + 1}`);
      assert.equal(a.moved + s.moved, moves[i], `${W}×${H} ${rule} move count ${i + 1}`);
    });
  }
});

const invariant = (net, s) => {
  for (let k = 0; k < s.pos.length; k++) if (s.pos[k] >= 0) assert.equal(s.occ[s.pos[k]], k);
  let n = 0;
  for (let c = 0; c < s.occ.length; c++) if (s.occ[c] >= 0) { n++; assert.equal(s.pos[s.occ[c]], c); assert.ok(net.road[c]); }
  assert.equal(n, onStreet(s));
};

test('maps: occupancy stays a bijection, car count is conserved, inputs are not mutated', () => {
  for (const [id, net] of nets)
    for (const rule of [CLASSIC, TRAIN]) {
      let s = init(net, Math.round(net.roadCells * 0.35), 7, { rule });
      const n = s.pos.length;
      for (let t = 0; t < 120; t++) {
        const before = s.occ.slice();
        const next = halfStep(net, s, { rule, slow: 0.1 });
        assert.deepEqual(s.occ, before, `${id} mutated input`);
        s = next;
        invariant(net, s);
        assert.equal(s.pos.length, n);
      }
    }
});

test('determinism: same seed, same orbit', () => {
  const [, net] = nets[0];
  const run = () => { let s = init(net, 300, 42); for (let i = 0; i < 50; i++) s = step(net, s, { slow: 0.2 }); return [...s.occ]; };
  assert.deepEqual(run(), run());
});

test('certificate soundness: a car certified frozen never moves again (rules × box rule × signals, with noise)', () => {
  for (const [id, net] of nets)
    for (const rule of [CLASSIC, TRAIN])
      for (const [rho, box, green] of [[0.3, false, 1], [0.5, false, 6], [0.3, true, 6], [0.5, true, 1]]) {
        const o = { rule, slow: 0.15, box, green, crossTurns: !box };
        let s = init(net, Math.round(net.roadCells * rho), 11, o);
        const frozenAt = new Map();
        for (let t = 0; t < 400; t++) {
          if (t % 50 === 0) s = breakDown(s, (t * 7) % s.pos.length, 60); // incidents only remove moves
          const { frozen } = certificate(net, s, o);
          frozen.forEach((f, k) => { if (f && !frozenAt.has(k)) frozenAt.set(k, [s.t, s.pos[k]]); });
          s = halfStep(net, s, o);
          for (const [k, [t0, p]] of frozenAt) assert.equal(s.pos[k], p, `${id} ${rule} ρ=${rho}: car ${k} frozen at ${t0} moved`);
        }
      }
});

test('every permanent core is a lane-graph cycle with at least girth cars (G1 analogue)', () => {
  for (const [, net] of nets) {
    let s = init(net, Math.round(net.roadCells * 0.6), 3);
    for (let t = 0; t < 200; t++) s = halfStep(net, s);
    for (const core of certificate(net, s).cores) {
      assert.ok(core.length >= girth(net));
      core.forEach((k, i) => assert.equal(s.next[k], s.pos[core[(i + 1) % core.length]]));
    }
  }
});

test('BML torus: a certified gridlock is a fixed point (G0) and full rings rotate under TRAIN', () => {
  const net = torus(4, 4);
  const jam = [[1, 1, 1, 1], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]; // G1 construction, n = 7 ≥ min(W,H)
  const s = fromGrid(net, jam);
  assert.ok(isGridlock(net, s));
  assert.deepEqual(toGrid(net, step(net, s, { rule: CLASSIC })), jam);
  assert.equal(certificate(net, s).count, 7);
  // TRAIN: the full east row is a single-axis cycle — it rotates, so it is not certified.
  assert.equal(certificate(net, s, { rule: TRAIN }).cores.length, 0);
  assert.equal(halfStep(net, s, { rule: TRAIN }).moved, 4);
});

test('towing a core car breaks its cycle; exiting cars re-enter (closed system)', () => {
  const [, net] = nets.find(([id]) => id === 'etoile');
  let s = init(net, Math.round(net.roadCells * 0.6), 5);
  for (let t = 0; t < 300; t++) s = halfStep(net, s);
  const { cores } = certificate(net, s);
  assert.ok(cores.length > 0, 'expected a jam at ρ = 0.6');
  const k = cores[0][0];
  const after = certificate(net, tow(s, k));
  assert.ok(!after.cores.some((c) => c.includes(k)));
  assert.equal(tow(s, k).pos[k], -1);
  let exited = 0;
  let u = init(net, 100, 9);
  for (let t = 0; t < 400; t++) { u = halfStep(net, u); exited = u.exited; }
  assert.ok(exited > 0 && onStreet(u) > 90, `exited ${exited}, on street ${onStreet(u)}`);
  assert.ok(![...u.next].some((x, k) => u.pos[k] >= 0 && x !== EXIT && !net.road[x]));
});

test('a broken-down car holds its cell for exactly its stall time, then drives on', () => {
  const [, net] = nets.find(([id]) => id === 'grachten');
  let s = init(net, 60, 4, { green: 6, box: true });
  for (let t = 0; t < 20; t++) s = halfStep(net, s, { green: 6, box: true });
  const k = s.pos.findIndex((p) => p >= 0);
  const [cell, t0] = [s.pos[k], s.t];
  s = breakDown(s, k, 40);
  for (let t = 0; t < 40; t++) { assert.ok(isStalled(s, k)); assert.equal(s.pos[k], cell); s = halfStep(net, s, { green: 6, box: true }); }
  assert.ok(!isStalled(s, k));
  for (let t = 0; t < 60 && s.pos[k] === cell; t++) s = halfStep(net, s, { green: 6, box: true });
  assert.notEqual(s.pos[k], cell, `stalled from ${t0}`);
});

test('lab JAM status is rule-aware: a full eastbound ring on a 3×3 torus is all-blocked yet rotates under TRAIN', () => {
  const net = torus(3, 3);
  const s = fromGrid(net, [[1, 1, 1], [0, 0, 0], [0, 0, 0]]);
  assert.ok(isGridlock(net, s), 'every target occupied');
  assert.equal(certificate(net, s, { rule: CLASSIC }).count, 3, 'CLASSIC: frozen');
  assert.equal(certificate(net, s, { rule: TRAIN }).count, 0, 'TRAIN: not frozen');
  assert.equal(halfStep(net, s, { rule: TRAIN }).moved, 3, 'TRAIN: the ring moves');
});
