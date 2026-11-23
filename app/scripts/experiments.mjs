// Experiments for docs/paper: every preset × traffic law × density × seed, plus the
// dynamics-free structure of each lane graph. Deterministic (seeded); writes
// docs/paper/data/experiments.json.   node scripts/experiments.mjs
import { readFile, writeFile } from 'node:fs/promises';
import { rasterize, girth } from '../src/raster.js';
import { PLACES, WINDOW } from '../src/presets.js';
import { init, halfStep, LAWS, DEFAULTS } from '../src/sim.js';
import { certificate, onStreet } from '../src/analysis.js';
import { jamGraph, girthOf, cycleCensus, cycleRisk, spectralRadius, throughputBound } from '../src/structure.js';

const RHOS = [0.1, 0.2, 0.3, 0.4, 0.5];
const SEEDS = [1, 2, 3, 4, 5];
const STEPS = 1200, BURN = 600, SLOW = 0.1;
const presets = JSON.parse(await readFile(new URL('../data/presets.json', import.meta.url)));
const lawOpts = (l) => ({ ...DEFAULTS, green: l.green, box: l.box, crossTurns: l.crossTurns, slow: SLOW });
const fin = (x) => (Number.isFinite(x) ? x : null);

const run = (net, o, rho, seed) => {
  let s = init(net, Math.round(net.roadCells * rho), seed, o);
  let [hops, dens, samples, t25] = [0, 0, 0, null];
  for (let t = 0; t < STEPS; t++) {
    s = halfStep(net, s, o);
    if (t >= BURN) { hops += s.moved; dens += onStreet(s); samples++; }
    if (t25 === null && t % 10 === 0 && certificate(net, s, o).count > 0.25 * onStreet(s)) t25 = t;
  }
  const rhoOn = dens / samples / net.roadCells;
  const v = (2 * hops) / Math.max(1, dens); // hops per car per full step
  return { rho: rhoOn, v, j: rhoOn * v, frozen: certificate(net, s, o).count / Math.max(1, onStreet(s)), t25 };
};

const places = presets.places.map((p) => {
  const net = rasterize(p.roads, { ...WINDOW, drive: PLACES.find((q) => q.id === p.id).drive });
  const laws = LAWS.map((l) => {
    const o = lawOpts(l);
    const J = jamGraph(net, o);
    const g = girthOf(J);
    const census = cycleCensus(J, { maxLen: Number.isFinite(g) ? Math.min(128, g + 8) : 16, budget: 3e6 });
    const runs = RHOS.map((rho) => ({ target: rho, seeds: SEEDS.map((seed) => run(net, o, rho, seed)) }));
    console.log(`${p.id} ${l.name} done`);
    return { law: l.name, jamGirth: fin(g), cycles: census.count, complete: census.complete, risk03: cycleRisk(census, 0.3), lambda: spectralRadius(J), runs };
  });
  return {
    id: p.id, name: p.name, drive: PLACES.find((q) => q.id === p.id).drive,
    cells: net.roadCells, edges: net.outList.length, junctions: net.junction.reduce((a, b) => a + b, 0), entries: net.entries.length,
    girth: fin(girth(net)), throughput: { classic: throughputBound(net, 'classic'), train: throughputBound(net, 'train') }, laws,
  };
});

await writeFile(new URL('../../docs/paper/data/experiments.json', import.meta.url), JSON.stringify({
  generated: 'app/scripts/experiments.mjs', window: WINDOW, steps: STEPS, burn: BURN, slow: SLOW, rhos: RHOS, seeds: SEEDS,
  source: presets.source, license: presets.license, fetched: presets.fetched, places,
}, null, 1));
