import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { rasterize } from '../src/raster.js';
import { PLACES, WINDOW } from '../src/presets.js';
import { init, halfStep, breakDown, LAWS, DEFAULTS, CLASSIC } from '../src/sim.js';
import { certificate } from '../src/analysis.js';
import { trapSet, safeCells, minGridlockVehicles, closureTimeBound, mfdEnvelope } from '../src/realflow.js';

const presets = JSON.parse(readFileSync(new URL('../data/presets.json', import.meta.url)));
const nets = presets.places.map((p) => [p.id, rasterize(p.roads, { ...WINDOW, drive: PLACES.find((q) => q.id === p.id).drive })]);
const law = (name, extra = {}) => { const l = LAWS.find((x) => x.name === name); return { ...DEFAULTS, green: l.green, box: l.box, crossTurns: l.crossTurns, slow: 0.1, ...extra }; };
const count = (a) => a.reduce((x, y) => x + y, 0);

test('R2: with commitment, the greatest trap is exactly the certified frozen set (CLASSIC, no box rule)', () => {
  for (const [id, net] of nets) {
    const o = law('BML LIGHTS');
    let s = init(net, Math.round(net.roadCells * 0.4), 3, o);
    for (let t = 0; t < 500; t++) { if (t % 100 === 0) s = breakDown(s, t % s.pos.length, 80); s = halfStep(net, s, o); }
    const trap = trapSet(net, s, o);
    const { frozen } = certificate(net, s, o);
    frozen.forEach((f, k) => assert.equal(trap[k], f ? 1 : 0, `${id}: car ${k}`));
  }
});

test('R2 under the box rule: the trap contains every certified car (it also sees box-path blocking)', () => {
  for (const [id, net] of nets)
    for (const name of ['CITY CODE', 'FREE TURNS']) {
      const o = law(name);
      let s = init(net, Math.round(net.roadCells * 0.3), 5, o);
      for (let t = 0; t < 500; t++) s = halfStep(net, s, o);
      const trap = trapSet(net, s, o);
      certificate(net, s, o).frozen.forEach((f, k) => assert.ok(!f || trap[k], `${id} ${name}: certified car ${k} not trapped`));
    }
});

test('R2: re-routing only shrinks the trap (options ⊇ the committed cell)', () => {
  for (const [id, net] of nets) {
    const o = law('BML LIGHTS');
    let s = init(net, Math.round(net.roadCells * 0.5), 4, o);
    for (let t = 0; t < 400; t++) s = halfStep(net, s, o);
    const [committed, rerouting] = [trapSet(net, s, o), trapSet(net, s, o, { reroute: true })];
    rerouting.forEach((r, k) => assert.ok(!r || committed[k], `${id}: car ${k}`));
  }
});

test('R2 soundness: under re-routing dynamics, a trapped car never moves again (laws × noise × breakdowns)', () => {
  for (const [id, net] of nets)
    for (const name of ['CITY CODE', 'FREE TURNS', 'BLOCK THE BOX', 'BML LIGHTS']) {
      const o = law(name, { reroute: true, rule: CLASSIC });
      let s = init(net, Math.round(net.roadCells * 0.5), 6, o);
      const trappedAt = new Map();
      for (let t = 0; t < 500; t++) {
        if (t % 70 === 0) s = breakDown(s, (t * 11) % s.pos.length, 60);
        trapSet(net, s, o, { reroute: true }).forEach((f, k) => {
          if (f && !trappedAt.has(k)) trappedAt.set(k, [s.pos[k], s.last[k]]);
        });
        s = halfStep(net, s, o);
        for (const [k, [pos, last]] of trappedAt) {
          assert.equal(s.pos[k], pos, `${id} ${name}: trapped car ${k} changed cell`);
          assert.equal(s.last[k], last, `${id} ${name}: trapped car ${k} recorded movement`);
        }
      }
    }
});

test('R2 safe cells: no trapped car ever sits on a safe cell; an all-safe map never has a trap', () => {
  for (const [id, net] of nets) {
    const o = law('BLOCK THE BOX', { reroute: true });
    const { safe, count: nSafe } = safeCells(net, o);
    let s = init(net, Math.round(net.roadCells * 0.55), 8, o);
    for (let t = 0; t < 600; t++) {
      s = halfStep(net, s, o);
      if (t % 20) continue;
      const trap = trapSet(net, s, o, { reroute: true });
      trap.forEach((f, k) => { if (f) assert.ok(!safe[s.pos[k]], `${id}: trapped car on safe cell`); });
      if (nSafe === net.roadCells) assert.equal(count(trap), 0, `${id}: all cells safe yet a trap exists`);
    }
  }
});

test('R1, R3, R5: closed forms', () => {
  assert.equal(minGridlockVehicles(4 * 15, 7.5), 8);       // a 15 m × 15 m crossing box
  assert.equal(minGridlockVehicles(720, 7.5), 96);         // around an 80 m × 280 m block
  assert.ok(Math.abs(closureTimeBound({ loopMetres: 720, n0: 29, inflowCapacity: 0.5 }) - 134) < 1e-9);
  assert.equal(closureTimeBound({ loopMetres: 60, n0: 20, inflowCapacity: 1 }), 0);
  assert.equal(mfdEnvelope({ accumulation: 100, vFree: 14, meanTrip: 2000, cutCapacity: 2 }), 0.7);
  assert.equal(mfdEnvelope({ accumulation: 1000, vFree: 14, meanTrip: 2000, cutCapacity: 2 }), 2);
});

test('R5 in simulation, exact on a finite window: completed trips × their mean length ≤ accumulation × mean speed ≤ accumulation × v_free', () => {
  for (const [id, net] of nets.slice(0, 3)) {
    const o = law('CITY CODE');
    let s = init(net, Math.round(net.roadCells * 0.3), 2, o);
    for (let t = 0; t < 400; t++) s = halfStep(net, s, o); // burn-in
    const hops = new Int32Array(s.pos.length).fill(-1); // hops of the trip in progress, −1 until a fresh spawn
    let [trips, tripHops, accum, allHops, T] = [0, 0, 0, 0, 1600];
    for (let t = 0; t < T; t++) {
      const n = halfStep(net, s, o);
      for (let k = 0; k < s.pos.length; k++) {
        if (s.pos[k] < 0 && n.pos[k] >= 0) hops[k] = 0; // spawned
        else if (s.pos[k] >= 0 && n.pos[k] !== s.pos[k]) { allHops++; if (hops[k] >= 0) hops[k]++; }
        if (s.pos[k] >= 0 && n.pos[k] < 0 && hops[k] >= 0) { trips++; tripHops += hops[k]; hops[k] = -1; }
      }
      accum += n.pos.reduce((a, p) => a + (p >= 0), 0);
      s = n;
    }
    const [steps, Nbar] = [T / 2, accum / T];
    const [lambda, vbar, ell] = [trips / steps, allHops / steps / Nbar, tripHops / trips];
    assert.ok(trips >= 10, `${id}: ${trips} trips`);
    assert.ok(lambda * ell <= Nbar * vbar + 1e-9, `${id}: λℓ=${lambda * ell} > N̄v̄=${Nbar * vbar}`); // no tolerance
    assert.ok(vbar <= 2, 'at most one hop per half-step');
    assert.ok(lambda <= mfdEnvelope({ accumulation: Nbar, vFree: 2, meanTrip: ell, cutCapacity: Infinity }) + 1e-9, `${id}: envelope`);
  }
});

test('R2 safe cells refuse the box rule, where the theorem does not apply', () => {
  assert.throws(() => safeCells(nets[0][1], law('CITY CODE')), /box rule/);
});
