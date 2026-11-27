// Theorems for real traffic flow: results that drop the lattice model's idealisations.
// Proofs: docs/research/2026-11-24-real-traffic-theorems.md.
//
//   trapSet          R2: permanent gridlock when drivers may re-route (OR-model deadlock)
//   safeCells        R2: rank certificates for freely re-routing cars, with no box rule
//   jamGirthMetres   R1: minimum gridlock size from physical loop length and jam spacing
//   closureTimeBound R3: earliest time a loop can lock, from mass conservation
//   mfdEnvelope      R5: Little's law + speed limit + cut capacity bound network flow
import { turnOptions, EXIT, aheadOf, CLASSIC, DEFAULTS } from './sim.js';

/** Options of car k, each as the list of cells that must be free for that move. Re-routing drivers
 * may take any legal option from their current lane, unless committed through a junction box;
 * committed drivers have one option. Under the box rule, entering a junction from outside also
 * needs the committed path through the box free (sim.boxClear). */
const optionsOf = (net, s, k, opts, reroute) => {
  const [pos, committed] = [s.pos[k], s.next[k]];
  const entersBox = opts.box && committed >= 0 && net.junction[committed] && !net.junction[pos];
  const need = (dest) => (dest === EXIT ? [] : [dest]);
  const current = entersBox ? [committed, ...aheadOf(s, k).filter((c) => c >= 0)] : need(committed);
  if (!reroute || s.aheadLen[k] || s.species[k]) return [current];
  // Planning can depend on the preceding heading. The committed move remains
  // available even when it is absent from the heading-free re-routing menu.
  const alternatives = turnOptions(net, pos, s.prev[k], opts).cells;
  return [current, ...alternatives.filter((c) => c !== committed).map(need)];
};

/** Project required cells to their current occupants. Temporary breakdowns,
 * red lights and contention can delay a move but do not remove it from this menu. */
export const trapInput = (net, s, opts, { reroute = false } = {}) => {
  const rules = { ...DEFAULTS, ...opts };
  const cars = [...s.pos.keys()].filter((k) => s.pos[k] >= 0);
  const menus = Array.from({ length: s.pos.length }, () => []);
  for (const k of cars)
    menus[k] = optionsOf(net, s, k, rules, reroute).map((need) => need.map((c) => s.occ[c]).filter((j) => j >= 0));
  return { cars, menus };
};

/** Greatest set whose members have a blocker for every option. A car with
 * zero options stays in the set. EXIT or a vacant option has zero blockers and
 * deletes that car. Each changing pass deletes at least one candidate. */
export const greatestTrap = ({ cars, menus }) => {
  const inS = new Uint8Array(menus.length);
  for (const k of cars) inS[k] = 1;
  for (let changed = true; changed;) {
    changed = false;
    for (const k of cars)
      if (inS[k] && menus[k].some((blockers) => blockers.every((j) => !inS[j]))) {
        inS[k] = 0;
        changed = true;
      }
  }
  return inS;
};

/** Under CLASSIC a trap remains immobile if stationary cars keep their
 * positions and their actual moves stay within the snapshot menus. */
export const trapSet = (net, s, opts, routing) => greatestTrap(trapInput(net, s, opts, routing));

/** One authoritative turn menu per legal arrival. The unknown-heading case
 * includes spawn and initialization with no in-lane. Include it also for
 * isolated roads so coverage does not rely on an empty arrival list. */
export const safeCellTurnTable = (net, opts) => {
  const rules = { ...DEFAULTS, ...opts };
  if (rules.box) throw new Error('safeCells: the safe-cell theorem assumes no box rule');
  if (rules.rule !== CLASSIC) throw new Error('safeCells: the safe-cell theorem assumes CLASSIC');
  const spawn = new Set(net.entries);
  return Array.from(net.road, (road, c) => {
    if (!road) return null;
    const arrivals = [...new Set(net.inList.subarray(net.inStart[c], net.inStart[c + 1]))];
    if (!arrivals.length || spawn.has(c) || !net.entries.length) arrivals.push(-1);
    return arrivals.map((prev) => ({ prev, cells: turnOptions(net, c, prev, rules).cells }));
  });
};

/** Construct a rank per safe cell. Ranks strictly decrease along one
 * witnessed move for every arrival, starting with actual map exits. */
export const safeCellRanks = (table) => {
  const ranks = Array(table.length).fill(null);
  for (let changed = true; changed;) {
    changed = false;
    for (const [c, arrivals] of table.entries()) {
      if (!arrivals || ranks[c] !== null) continue;
      const witness = arrivals.map(({ cells }) => cells.find((q) => q === EXIT || ranks[q] != null));
      if (witness.includes(undefined)) continue;
      ranks[c] = witness.reduce((r, q) => (q === EXIT ? r : Math.max(r, ranks[q] + 1)), 0);
      changed = true;
    }
  }
  return ranks;
};

/** Verify the least-fixed-point certificate against the supplied network.
 * A rank needs a strict descent witness for every arrival. An unranked road
 * needs one arrival with neither an exit nor any ranked destination. */
export const checkSafeCellRanks = (table, ranks) => {
  if (!Array.isArray(ranks) || ranks.length !== table.length) return false;
  return table.every((arrivals, c) => {
    const rank = ranks[c];
    if (!arrivals) return rank === null;
    if (!arrivals.length) return false;
    if (rank === null)
      return arrivals.some(({ cells }) => cells.every((q) => q !== EXIT && ranks[q] === null));
    return Number.isSafeInteger(rank) && rank >= 0 &&
      arrivals.every(({ cells }) => cells.some((q) => q === EXIT || (ranks[q] != null && ranks[q] < rank)));
  });
};

export const verifySafeCellCertificate = (net, opts, ranks) => checkSafeCellRanks(safeCellTurnTable(net, opts), ranks);

/** Least safe set under no-box re-routing. An all-ranked map rules out
 * structural traps for a fleet with the certified arrival menus. */
export const safeCells = (net, opts) => {
  const ranks = safeCellRanks(safeCellTurnTable(net, opts));
  const safe = Uint8Array.from(ranks, (rank) => Number(rank !== null));
  return { safe, ranks, count: safe.reduce((a, b) => a + b, 0), roadCells: net.roadCells };
};

/** R1. Fewest vehicles in a gridlock around a committed loop of physical length L (m), with jam
 * spacing sJam (m, front-to-front at standstill): ⌈L / sJam⌉. */
export const minGridlockVehicles = (loopMetres, sJam = 7.5) => Math.ceil(loopMetres / sJam - 1e-9);

/** R1 on a lane graph: girth in cells × cell length = the shortest committed loop in metres. */
export const jamGirthMetres = (girthCells, cellMetres) => girthCells * cellMetres;

/** R3. A loop of length L (m) holding n0 vehicles cannot lock before
 * (L / sJam − n0) / inflowCapacity, where inflowCapacity (veh/s) bounds the net inflow into it. */
export const closureTimeBound = ({ loopMetres, n0, inflowCapacity, sJam = 7.5 }) =>
  Math.max(0, (loopMetres / sJam - n0) / inflowCapacity);

/** R5. Upper envelope of the network flow (trips completed per unit time) at mean accumulation N:
 * min(N · vFree / meanTrip, cutCapacity). */
export const mfdEnvelope = ({ accumulation, vFree, meanTrip, cutCapacity }) =>
  Math.min((accumulation * vFree) / meanTrip, cutCapacity);
