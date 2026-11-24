// Re-routing experiment for docs/research/2026-11-24-real-traffic-theorems.md: for each preset and
// traffic law, the share of safe cells (R2) and, with and without re-routing, the trapped share
// and the flow after 1200 half-steps. Deterministic; writes docs/research/data/2026-11-24-reroute.json.
import { readFile, writeFile } from 'node:fs/promises';
import { rasterize } from '../src/raster.js';
import { PLACES, WINDOW } from '../src/presets.js';
import { init, halfStep, LAWS, DEFAULTS } from '../src/sim.js';
import { onStreet } from '../src/analysis.js';
import { trapSet, safeCells } from '../src/realflow.js';

const [RHOS, SEEDS, STEPS, BURN] = [[0.2, 0.3, 0.4], [1, 2, 3, 4, 5], 1200, 600];
const presets = JSON.parse(await readFile(new URL('../data/presets.json', import.meta.url)));
const mean = (a) => a.reduce((x, y) => x + y, 0) / a.length;

const run = (net, o, rho, seed) => {
  let s = init(net, Math.round(net.roadCells * rho), seed, o);
  let [hops, dens] = [0, 0];
  for (let t = 0; t < STEPS; t++) { s = halfStep(net, s, o); if (t >= BURN) { hops += s.moved; dens += onStreet(s); } }
  const trapped = trapSet(net, s, o, { reroute: o.reroute }).reduce((a, b) => a + b, 0) / Math.max(1, onStreet(s));
  const rhoOn = dens / (STEPS - BURN) / net.roadCells;
  return { trapped, j: (rhoOn * 2 * hops) / Math.max(1, dens) };
};

const out = presets.places.map((p) => {
  const net = rasterize(p.roads, { ...WINDOW, drive: PLACES.find((q) => q.id === p.id).drive });
  return {
    id: p.id,
    laws: LAWS.map((l) => {
      const base = { ...DEFAULTS, green: l.green, box: l.box, crossTurns: l.crossTurns, slow: 0.1 };
      const safeShare = base.box ? null : safeCells(net, base).count / net.roadCells; // theorem needs no box rule
      const res = (reroute) => RHOS.map((rho) => {
        const r = SEEDS.map((seed) => run(net, { ...base, reroute }, rho, seed));
        return { rho, trapped: mean(r.map((x) => x.trapped)), j: mean(r.map((x) => x.j)) };
      });
      console.log(p.id, l.name);
      return { law: l.name, box: base.box, safeShare, committed: res(false), rerouting: res(true) };
    }),
  };
});
await writeFile(new URL('../../docs/research/data/2026-11-24-reroute.json', import.meta.url),
  JSON.stringify({ generated: 'app/scripts/reroute.mjs', rhos: RHOS, seeds: SEEDS, steps: STEPS, burn: BURN, places: out }, null, 1));
