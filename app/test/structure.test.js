import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { rasterize, torus, girth } from '../src/raster.js';
import { PLACES, WINDOW } from '../src/presets.js';
import { init, halfStep, LAWS, DEFAULTS, CLASSIC, TRAIN } from '../src/sim.js';
import { certificate } from '../src/analysis.js';
import { jamGraph, cellGraph, girthOf, cycleCensus, cycleRisk, spectralRadius, throughputBound, cuttingWord, freeSpeed, traversalTime } from '../src/structure.js';

const presets = JSON.parse(readFileSync(new URL('../data/presets.json', import.meta.url)));
const nets = presets.places.map((p) => [p.id, rasterize(p.roads, { ...WINDOW, drive: PLACES.find((q) => q.id === p.id).drive })]);
const law = (name) => { const l = LAWS.find((x) => x.name === name); return { ...DEFAULTS, green: l.green, box: l.box, crossTurns: l.crossTurns, slow: 0.1 }; };

test('cell-graph girth matches raster.girth; jam-graph girth is never smaller', () => {
  for (const [id, net] of nets) {
    assert.equal(girthOf(cellGraph(net)), girth(net), id);
    for (const name of ['CITY CODE', 'BML LIGHTS']) assert.ok(girthOf(jamGraph(net, law(name))) >= girth(net), `${id} ${name}`);
  }
});

test('turning probabilities are substochastic and leak only at exits', () => {
  for (const [, net] of nets.slice(0, 2)) {
    const L = jamGraph(net, law('CITY CODE'));
    L.succ.forEach((out, i) => {
      const mass = out.reduce((a, [, p]) => a + p, 0);
      assert.ok(mass <= 1 + 1e-9);
      if (!net.exit[L.head[i]] && out.some(([, p]) => p > 0)) assert.ok(Math.abs(mass - 1) < 1e-9, `mass ${mass}`);
    });
    const lam = spectralRadius(L);
    assert.ok(lam >= 0 && lam <= 1 + 1e-9, `λ=${lam}`);
    assert.equal(lam > 1e-9, Number.isFinite(girthOf({ succ: L.succ.map((o) => o.filter(([, p]) => p > 0)) })), 'λ > 0 iff the routed graph has a cycle');
  }
});

test('every direct jam core seen in simulation is a cycle of the jam graph, so has ≥ girth(J) cars', () => {
  for (const [id, net] of nets) {
    const o = { ...law('BML LIGHTS'), box: false };
    const g = girthOf(jamGraph(net, o));
    let s = init(net, Math.round(net.roadCells * 0.5), 2, o);
    for (let t = 0; t < 600; t++) s = halfStep(net, s, o);
    const J = jamGraph(net, o);
    const at = new Map(J.head.map((c, i) => [c, i]));
    for (const core of certificate(net, s, o).cores) {
      assert.ok(core.length >= g, `${id}: core ${core.length} < girth ${g}`);
      core.forEach((k) => assert.ok(J.succ[at.get(s.pos[k])].some(([j]) => J.head[j] === s.next[k]), `${id}: hop not in J`));
    }
  }
});

test('census: the torus has exactly min(W,H)-cycles at the girth; risk is monotone in ρ', () => {
  const net = torus(5, 3);
  const c = cycleCensus(cellGraph(net), { maxLen: 3 });
  assert.ok(c.complete);
  assert.equal(Math.min(...c.byLength.keys()), 3);
  assert.equal(c.shortest.filter((x) => x.cells.length === 3).length, 5, 'five vertical rings of length H = 3');
  const L = jamGraph(nets.find(([id]) => id === 'bank')[1], law('BML LIGHTS'));
  const census = cycleCensus(L, { maxLen: 12 });
  assert.ok(census.count > 0);
  assert.ok(cycleRisk(census, 0.2) < cycleRisk(census, 0.4));
  assert.ok(census.shortest.every(({ cells }) => new Set(cells).size === cells.length));
});

test('throughput lemma: under CLASSIC a non-entry cell is entered at most once per two half-steps', () => {
  for (const [id, net] of nets.slice(0, 3)) {
    const o = law('BML LIGHTS');
    let s = init(net, Math.round(net.roadCells * 0.4), 5, o);
    const lastEntry = new Int32Array(net.W * net.H).fill(-9);
    const isEntry = new Set(net.entries);
    for (let t = 0; t < 400; t++) {
      const next = halfStep(net, s, o);
      for (let k = 0; k < s.pos.length; k++)
        if (next.pos[k] >= 0 && next.pos[k] !== s.pos[k] && s.pos[k] >= 0) {
          const c = next.pos[k];
          if (!isEntry.has(c)) { assert.ok(s.t - lastEntry[c] >= 2, `${id}: cell ${c} entered at ${lastEntry[c]} and ${s.t}`); lastEntry[c] = s.t; }
        }
      s = next;
    }
  }
});

test('throughput bound: finite and positive; the measured exit rate never exceeds it', () => {
  for (const [id, net] of nets) {
    for (const rule of [CLASSIC, TRAIN]) {
      const k = throughputBound(net, rule);
      assert.ok(k > 0 && k <= 2 * net.entries.length, `${id} ${rule} bound=${k}`);
      const o = { ...law('BML LIGHTS'), rule, slow: 0 };
      let s = init(net, Math.round(net.roadCells * 0.3), 9, o);
      for (let t = 0; t < 400; t++) s = halfStep(net, s, o);
      const e0 = s.exited;
      for (let t = 0; t < 1200; t++) s = halfStep(net, s, o);
      assert.ok((s.exited - e0) / 600 <= k, `${id} ${rule}: ${(s.exited - e0) / 600} > ${k}`);
    }
  }
});

test('Sturmian streets: the raster word has the predicted switch rate and free speed', () => {
  for (const deg of [0, 10, 26.565, 37, 45, 63.4, 80, 90, 135, 200]) {
    const th = (deg * Math.PI) / 180;
    const w = cuttingWord(th, 4000);
    const switches = w.slice(1).filter((a, i) => a !== w[i]).length / (w.length - 1);
    const fs = freeSpeed(th);
    assert.ok(Math.abs(switches - fs.switchRate) < 2e-3, `${deg}°: switch ${switches} vs ${fs.switchRate}`);
    const speed = (2 * w.length) / traversalTime(w);
    assert.ok(Math.abs(speed - fs.cells) < 2e-3, `${deg}°: speed ${speed} vs ${fs.cells}`);
  }
});

test('Sturmian free speed matches the simulator: one car on a straight diagonal one-way street', () => {
  const deg = 26.565; // slope 1/2
  const th = (deg * Math.PI) / 180;
  const L = 3000;
  const net = rasterize([{ o: 1, c: 4, pts: [-Math.cos(th) * L, -Math.sin(th) * L, Math.cos(th) * L, Math.sin(th) * L].map((v) => Math.round(v * 10)) }], { cols: 200, rows: 120, cell: 7.5 });
  const o = { ...DEFAULTS, green: 1, slow: 0, straight: 1e9 };
  let s = init(net, 1, 1, o);
  const moved = [];
  for (let t = 0; t < 120; t++) { const n = halfStep(net, s, o); if (n.pos[0] !== s.pos[0] && n.pos[0] >= 0 && s.pos[0] >= 0) moved.push(t); s = n; }
  const span = moved.at(-1) - moved[0];
  const speed = (2 * (moved.length - 1)) / span;
  assert.ok(Math.abs(speed - freeSpeed(th).cells) < 0.08, `simulated ${speed} vs predicted ${freeSpeed(th).cells}`);
});
