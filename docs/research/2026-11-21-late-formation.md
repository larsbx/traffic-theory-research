# When does the jam's seed form? Measured formation times of the first mixed cycle

**Research note — 21 November 2026. Empirical; no theorem, no novelty claim.**

Every fixed-density bound in the repository controls the first appearance of a mixed simple
direct-blocker cycle only up to some horizon:
- order √(log L) in the [diagonal-cut note](2026-11-18-diagonal-cuts.md);
- c·log L with c < 1/(6·log(2/p)) in the
  [guarded-barrier note](2026-11-19-guarded-barrier-formation.md).

A positive critical-density theorem would need control of formation at *all* later times. This
note measures when formation actually happens, to see how far the proven horizon is from the
real one.

CLASSIC rule, L×L torus, iid initial law (1 − p, p/2, p/2). T_M is the first round at which a
mixed simple direct-blocker cycle is present. Such a cycle never moves again and captures the
torus ([nucleation note](2026-11-18-freezing-gridlock-nucleation.md)).

## Method

`bml.late_formation.mixed_cycle_present` detects a mixed cycle in a whole batch at once:
- **Blocker map:** an occupied cell points to the cell ahead if that cell is occupied, and to a
  sink otherwise.
- **Pointer doubling** sends every cell onto a cycle or into the sink.
- **Mixed test:** a mixed cycle exists iff some cycle cell holds an E car blocked by an N car,
  because a pure cycle is a full row or column and has no such turn.
- **Validation:** it agrees with the per-state finder `bml.capture.find_blocker_cycles` on random
  states up to 6×6, and a test checks that a cycle, once present, persists.

`formation_sweep` runs a batch for a fixed horizon, testing for a mixed cycle every `every`
rounds, so T_M is known up to that resolution. It also records whether each sample is a
nonempty fixed point at the horizon. Raw data: `data/late-formation.json`, 28 (L, p) settings.

## Results

**Moderate densities** (horizon 100L, resolution L/8; 200 samples, 100 at L = 128). "≤ L" counts
formations within L rounds; "> 80L" counts formations in the last fifth of the horizon.

| L | p | formed | T_M/L quartiles | ≤ log L | ≤ L | > 80L |
|---|---|---|---|---|---|---|
| 16 | 0.40 | 11/200 | 9.6, 33.6, 61.3 | 0 | 0 | 2 |
| 32 | 0.40 | 21/200 | 10.3, 51.4, 80.9 | 0 | 0 | 6 |
| 64 | 0.40 | 90/200 | 11.7, 37.1, 65.1 | 0 | 0 | 7 |
| 128 | 0.40 | 70/100 | 4.2, 6.1, 14.1 | 0 | 0 | 3 |
| 16 | 0.45 | 65/200 | 7.6, 19.1, 53.3 | 0 | 1 | 7 |
| 32 | 0.45 | 165/200 | 7.1, 21.4, 46.4 | 0 | 1 | 9 |
| 64 | 0.45 | 197/200 | 3.5, 5.6, 13.9 | 0 | 0 | 2 |
| 128 | 0.45 | 97/100 | 3.0, 4.6, 6.3 | 0 | 0 | 1 |
| 16 | 0.50 | 155/200 | 4.9, 12.1, 34.6 | 0 | 0 | 7 |
| 32 | 0.50 | 196/200 | 3.0, 5.1, 10.1 | 0 | 3 | 1 |
| 64 | 0.50 | 200/200 | 2.3, 3.4, 4.6 | 0 | 2 | 0 |
| 128 | 0.50 | 100/100 | 1.9, 2.6, 3.5 | 0 | 1 | 0 |

At p = 0.35, mixed cycles formed in 1, 0, 1 of 200 samples at L = 16, 32, 64, and in 9 of 100 at
L = 128.

**High densities** (horizon 10L, resolution 1; every sample formed). Median T_M:

| p | L = 16 | 32 | 64 | 128 | fit of the median | proven c* in τ_M > c·log L |
|---|---|---|---|---|---|---|
| 0.70 | 19 | 27 | 37 | 48.5 | −21.3 + 14.2·ln L | < 0.159 |
| 0.90 | 5 | 6 | 8 | 10 | −2.1 + 2.45·ln L | < 0.209 |
| 0.97 | 1 | 2 | 3 | 4 | −3.0 + 1.44·ln L | < 0.230 |

## Findings

1. **Formation and freezing coincide.** In all 28 settings, "a mixed cycle formed by the horizon"
   and "frozen at the horizon" agree sample by sample. This matches the exact identity
   M = J ∩ Rᶜ of the [probability note](2026-11-18-probabilistic-gridlock-bounds.md); the
   full-lane event R is negligible at these sizes.
2. **The formation time scale depends on density, in three regimes:**
   - *Deep jamming* (p ≥ 0.9): **logarithmic.** The median grows by about 1–2 rounds per
     doubling of L. So the proven c·log L delay looks **sharp in order** here, with a constant
     smaller than the measured slope by a factor of about 6–10.
   - *Intermediate* (p ≈ 0.45–0.5 at L ≥ 64): **order L.** The median T_M/L falls with L towards
     a constant, about 2.6 at p = 0.5 and L = 128. At p = 0.7 the scale is sublinear but well
     above log L.
   - *Near the finite-size threshold* (p ≈ 0.35–0.40): **broad and heavy-tailed.** The quartiles
     of T_M/L span roughly 4 to 80, and a noticeable fraction forms after 80L rounds.
3. **Nothing forms within log L rounds at p ≤ 0.5.** Of roughly 1,380 formations at
   p ∈ [0.35, 0.5], none came within log L rounds and only 8 within L rounds. There the proven
   horizon falls short of the real formation time by at least a factor L/log L.
4. **The measured threshold drifts with L.** At fixed p = 0.35 and 0.40, the fraction formed within
   100L rounds grows with L, for example 1/200 → 9/100 at p = 0.35. So either the finite-size
   threshold decreases with L, or the 100L horizon is too short at small L, or both. This is the
   non-commutation of size and time limits proved in the probability note, now seen in data.

## What this does and does not show

- **For a proof.** At densities that matter for p₋ > 0, a fixed-density low-density theorem must
  control loop formation over times of order L, and near the threshold well beyond. Extending
  the present early-time union bounds from log L to a constant multiple of log L cannot suffice
  there. At high density the logarithmic bounds already have the right order.
- **Evidence only.** These are finite-sample Monte Carlo measurements on L ≤ 128 with censored
  horizons; each p ≤ 0.5 setting has at most 200 samples. They prove nothing asymptotic. They
  estimate neither p_c nor whether p₋ > 0.
- **Censoring.** "Formed by 100L" is a lower bound on eventual gridlock: some near-threshold
  samples could still jam later.
