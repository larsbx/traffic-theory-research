import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { rasterize } from '../src/raster.js';
import { PLACES, WINDOW } from '../src/presets.js';
import { breakDown, DEFAULTS, EXIT, halfStep, init, LAWS } from '../src/sim.js';
import { checkSafeCellRanks, greatestTrap, safeCellRanks, safeCellTurnTable, trapInput, trapSet } from '../src/realflow.js';

const schema = 'traffic.r2.map-certificates.v1';
const presets = JSON.parse(readFileSync(new URL('../data/presets.json', import.meta.url)));
const networks = presets.places.map(({ id, roads }) => [
  id, rasterize(roads, { ...WINDOW, drive: PLACES.find((place) => place.id === id).drive }),
]);
const describe = (id, law, net) => ({
  id, law: law.name, width: net.W, height: net.H, table: safeCellTurnTable(net, law),
});
const presetTables = () => networks.flatMap(([id, net]) =>
  LAWS.filter((law) => !law.box).map((law) => describe(id, law, net)));

function generate() {
  const maps = presetTables().map((map) => ({ ...map, ranks: safeCellRanks(map.table) }));
  verify({ schema, maps });
  return { schema, maps };
}

function verify(bundle) {
  const tables = presetTables();
  assert.equal(bundle.schema, schema);
  assert.equal(bundle.maps.length, tables.length);
  for (const [i, current] of tables.entries()) {
    const { ranks, ...saved } = bundle.maps[i];
    assert.deepEqual(saved, current, `${current.id} ${current.law}: source table changed`);
    assert.ok(checkSafeCellRanks(current.table, ranks), `${current.id} ${current.law}: invalid ranks`);
  }
}

const subset = (values, mask) => values.filter((_, i) => mask & (1 << i));
const allSubsets = (values) => Array.from({ length: 2 ** values.length }, (_, n) => subset(values, n));
const members = (bits) => Array.from(bits).flatMap((bit, car) => bit ? [car] : []);

// Enumerate every candidate subset as an independent oracle for deletion.
function trapControls() {
  const cars = allSubsets([0, 1]);
  const menus = allSubsets(cars);
  return cars.flatMap((universe) => menus.flatMap((a) => menus.map((b) => {
    const input = { cars: universe, menus: [a, b] };
    const union = new Set();
    for (const candidate of allSubsets(universe)) {
      if (candidate.every((k) => input.menus[k].every((o) => o.some((j) => candidate.includes(j)))))
        for (const car of candidate) union.add(car);
    }
    const expected = universe.filter((k) => union.has(k));
    assert.deepEqual(members(greatestTrap(input)), expected);
    return { ...input, expected };
  })));
}

// For each turn table, independently intersect all pre-fixed sets and check
// the structural theorem in all nine occupancy/arrival assignments.
function rankControls() {
  const choices = allSubsets([EXIT, 0, 1]);
  const rows = choices.flatMap((spawn) => choices.map((arriving) => [
    { prev: -1, cells: spawn }, { prev: 0, cells: arriving },
  ]));
  let assignments = 0;
  const maps = rows.flatMap((left, i) => rows.map((right, j) => {
    const table = [left, right];
    const ranks = safeCellRanks(table);
    const enabled = (mask) => table.reduce((result, arrivals, c) =>
      arrivals.every(({ cells }) => cells.some((q) => q === EXIT || (mask & (1 << q))))
        ? result | (1 << c) : result, 0);
    let least = 3;
    for (let mask = 0; mask < 4; mask++)
      if ((enabled(mask) & ~mask) === 0) least &= mask;
    const ranked = ranks.map((rank) => rank !== null);
    assert.deepEqual(ranked, [Boolean(least & 1), Boolean(least & 2)]);
    assert.equal(enabled(least), least);
    assert.ok(checkSafeCellRanks(table, ranks));

    for (const a of [-1, 0, 1]) for (const b of [-1, 0, 1]) {
      const arrivals = [a, b];
      const cars = [0, 1].filter((c) => arrivals[c] >= 0);
      const menus = table.map((row, c) => arrivals[c] < 0 ? [] :
        row[arrivals[c]].cells.map((q) => q === EXIT || arrivals[q] < 0 ? [] : [q]));
      assert.ok(members(greatestTrap({ cars, menus })).every((k) => !ranked[k]));
      assignments++;
    }
    return { id: `two-cells-${i}-${j}`, law: 'synthetic', width: 2, height: 1, table, ranks };
  }));
  return { maps, assignments };
}

function simulatorControls() {
  const cases = [];
  for (const [, net] of networks) for (const law of LAWS) for (const reroute of [false, true]) {
    const opts = { ...DEFAULTS, ...law, reroute, slow: 0.1 };
    const routing = { reroute };
    let s = init(net, Math.round(net.roadCells * 0.35), 17, opts);
    for (const start of [0, 24, 48]) {
      while (s.t < start) s = halfStep(net, s, opts);
      s = breakDown(s, start % s.pos.length, 8);
      cases.push({ ...trapInput(net, s, opts, routing), expected: members(trapSet(net, s, opts, routing)) });
    }
  }
  return cases;
}

function rejectionControls(map) {
  const rank = map.ranks.findIndex((value) => value > 0);
  const badRank = map.ranks.with(rank, 0);
  const missingRank = map.ranks.with(map.ranks.indexOf(0), null);
  const nonroadRank = map.ranks.with(map.table.indexOf(null), 0);
  const missingArrival = map.table.with(rank, []);
  const badTarget = map.table.with(rank, [{ prev: -1, cells: [map.table.length] }]);
  const cases = [
    { ...map, ranks: badRank }, { ...map, ranks: missingRank }, { ...map, ranks: nonroadRank },
    { ...map, ranks: map.ranks.slice(1) }, { ...map, table: missingArrival }, { ...map, table: badTarget },
  ];
  for (const candidate of cases)
    assert.equal(checkSafeCellRanks(candidate.table, candidate.ranks), false);
  return cases;
}

function checkLean(verifier, directory) {
  const bundle = generate();
  const { maps, assignments } = rankControls();
  const traps = trapControls();
  const snapshots = simulatorControls();
  const rejectedMaps = rejectionControls(bundle.maps[0]);
  assert.equal(maps.length, 4096);
  assert.equal(assignments, 36864);
  assert.equal(traps.length, 1024);
  assert.equal(bundle.maps.length, 12);
  assert.equal(snapshots.length, 144);
  const coverage = bundle.maps.map(({ id, law, table, ranks }) => ({
    id, law, roads: table.filter(Boolean).length, ranked: ranks.filter(Number.isInteger).length,
  }));
  assert.ok(coverage.every(({ roads, ranked }) => roads > 0 && roads === ranked));

  mkdirSync(directory, { recursive: true });
  writeFileSync(join(directory, 'r2-map-certificates.json'), JSON.stringify(bundle) + '\n');
  const input = join(directory, 'r2-lean-cases.json');
  writeFileSync(input, JSON.stringify({
    maps: [...bundle.maps, ...maps], rejectedMaps, traps: [...traps, ...snapshots],
  }) + '\n');
  const lean = spawnSync(verifier, [input], { encoding: 'utf8', timeout: 120000 });
  if (lean.error) throw lean.error;
  assert.equal(lean.status, 0, lean.stderr || lean.stdout);
  console.log(JSON.stringify({
    coverage, abstractTrapCases: traps.length, simulatorSnapshots: snapshots.length,
    abstractMaps: maps.length, occupancyArrivalAssignments: assignments,
    rejectedCertificates: rejectedMaps.length, lean: lean.stdout.trim(),
  }));
}

const args = process.argv.slice(2);
if (!args.length) {
  console.log(JSON.stringify(generate()));
} else if (args.length === 2 && args[0] === '--verify') {
  verify(JSON.parse(readFileSync(args[1], 'utf8')));
  console.log('Verified preset rank certificates against the current turn tables.');
} else if (args.length === 3 && args[0] === '--check-lean') {
  checkLean(args[1], args[2]);
} else {
  throw new Error('usage: r2-certificates.mjs [--verify FILE | --check-lean LEAN_EXE ARTIFACT_DIR]');
}
