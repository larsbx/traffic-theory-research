# From maximal cores to stopped original cars: formal count and mass reduction

**Research note — 21 November 2026.** This closes the count bridge and the
finite initial-weight comparison left in prose in the
[maximal-core note](2026-11-19-maximal-core-and-path-mass.md). It formalizes
that existing argument for the actual CLASSIC kernel. It does not establish
the remaining fixed-positive-density nonjamming estimate or claim new
probabilistic mathematics.

## 1. The counted objects

Let `s` be a complete configuration on a finite `W × H` torus, `F` the actual
east-then-north CLASSIC round, and `N(s)` its conserved population. Write:

- `K(s)` for the maximal occupied successor-closed spatial core, including
  paths feeding cycles;
- `Z(s)` for the number of **initially occupied original tags** whose actual
  traces eventually stay at a single site;
- `J(s)` for eventual **nonempty** gridlock;
- `R(s)` for an initial full east row or full north column.

`BML/StoppedCore.lean` defines executable `pathCoreFlag` and `pathCoreCount`
using the exact `N`-edge path test already proved in `PathCore.lean`. This
checks `N+1` occupied vertices, including the root. It separately defines
the semantic, noncomputable `stoppedCarCount` by filtering the original
species lists with `TagEventuallyStopped`. No eventual-stop decision oracle
is used by the executable checker.

## 2. The cardinality theorem

The main statement is:

```lean
theorem pathCoreCount_eventually_eq_stoppedCarCount
    {w h : Nat} (east north : Direction (Position w h))
    (s : Config (Position w h)) :
    ∃ start, ∀ t,
      pathCoreCount east north
        (iterate (step east north) (start+t) s) =
      stoppedCarCount east north s
```

It holds for the existing CLASSIC `step` on finite positions with arbitrary
supplied directions. The torus results instantiate these with the actual
east and north directions and require positive width and height.

The proof has four parts:

1. `speciesCells_carTrace_perm` uses the existing preservation, injectivity,
   and surjectivity theorems to permute current cars of each species with
   the actual traces of that species' original cars.
2. Filtering this permutation by current core membership proves
   `pathCoreCount_eq_tracedCoreCount` at **every** checkpoint. The auxiliary
   `pathCoreCount_eq_length_filter` proves that summing the two species
   really counts the spatial core sites.
3. `carTrace_eq_of_pathCoreMember` proves that entering a core freezes that
   same tag immediately. It uses `PermanentFrom.no_round_move` and actual
   `roundTransport`; persistent colored occupancy alone is not substituted
   for identity preservation.
4. The existing stopped-tag/core-entry equivalence and finite-list
   uniformization supply one time after which the two filters agree for
   all original cars. The species counts then add.

The related finite-time inequality is also formal:

\[
 |K(F^t(s))|\le Z(s)\qquad\text{for every }t.
\]

An initial snapshot can therefore underestimate the eventual stopped
population. The new theorem asserts equality from some finite time onward,
without supplying an effective or size-uniform deadline.

## 3. The pointwise jam comparison

For positive rectangles, `stoppedCarCount_jam_bounds` proves

\[
 N(s)\mathbf 1_{J(s)}\le Z(s)
 \le N(s)\mathbf 1_{J(s)}+N(s)\mathbf 1_{R(s)}.
\]

On an eventual nonempty jam, every original car stops. Off both `J` and `R`,
the existing `hasEventuallyStoppedCar_iff_jam_or_full_lane` theorem excludes
every stopped original tag. On the exceptional full-lane event, the ordinary
bound `Z≤N` is sufficient. The lane event belongs to the original board;
the proof does not evaluate it under a newly independent evolved law.

Empty boards and singleton dimensions are included. In particular, the
vacuous statement that all cars of an empty board stop is not used to infer
nonempty jam. `eventuallyJammed_carCount_pos` makes the positive-population
premise explicit wherever normalization needs it.

## 4. Exact finite initial weights

The project has no external mathematics package. `BML/CoreMass.lean` extends
the existing finite `Nat`-weight `Absorption.mass` interface with an exact
common population denominator. Set `A=W*H` and

\[
 D=\texttt{populationDenominator}(A)=A!>0.
\]

`population_dvd_denominator` and `population_scale_exact` prove that every
`1≤N≤A` divides `D` and `(D/N)*N=D`. Thus the natural-number division in
the definition is exact. At `N=0`, the score is zero.

For a finite support list `S` and initial weights `w(s) : Nat`, define

\[
 M_J=\sum_{s\in S}w(s)\mathbf 1_{J(s)},\qquad
 M_R=\sum_{s\in S}w(s)\mathbf 1_{R(s)},\qquad
 M_Z=\sum_{s\in S}w(s)\frac{D}{N(s)}Z(s),
\]

with the zero-population convention just stated. The actual Lean theorem
`normalizedStoppedMass_gridlock_bounds` is the cleared-denominator result

\[
 D M_J\le M_Z\le D(M_J+M_R).
\]

Repeated support entries count with multiplicity. Zero weights and zero
total weight are valid for this mass inequality. A probability law requires
`M=Σw(s)>0`; dividing by `D*M` then gives the rational interpretation

\[
 q\le\mathbb E[Z/N;N>0]\le q+\mathbb P(R).
\]

This last division is an interpretation of the proved integer inequality;
the module does not add a separate `Rat`- or `Real`-valued expectation
theorem. All finite rational initial laws can be represented by integer
weights after a common rescaling.

`normalizedCoreMass_eventually_eq_stoppedMass` first obtains a common
stabilization time for every board in the finite support, then proves
exact equality of the corresponding weighted core mass and `M_Z` for all
later rounds. `normalizedCoreMass_eventual_gridlock_bounds` combines the
two conclusions. Both `w(s)` and `N(s)` remain attached to the **initial**
board; only `|K(F^t(s))|` evolves.

## 5. Dependencies and verification contract

| Component | Dependencies and role |
|---|---|
| `BML/StoppedCore.lean` | Imports `BML.PathCore`; uses its actual-kernel core and fixation results plus species-wise car transport and finite counting. |
| `BML/CoreMass.lean` | Imports `StoppedCore`, `Absorption`, and `FiniteSums`; uses finite natural-number sums and divisibility. |
| `StoppedCoreExport.lean` | Evaluates cached actual boards and tag lists. `eval_board`, `eval_eastTags`, `eval_northTags`, and `coreTagCount_eq_tracedCoreCount` prove refinement to the original kernel and traces. `fullLaneCheck_iff` proves the initial-lane test. |
| Audits and acceptance | Main axiom audit requires the new count/mass theorems; a separate exporter audit checks its transitive axioms. The finite-BML workflow runs both the new audit and the replay. |

No movement definitions, dependency versions, obstruction theorems, or
existing theorem hypotheses change. The audit permits only `propext`,
`Quot.sound`, and `Classical.choice`; no new axiom or `sorry` is admitted.

The new acceptance command compares all 19,785 initial boards on `1×1`,
`1×2`, `2×1`, `2×2`, and `3×3` at their initial and independently determined
labeled-recurrence checkpoints. It compares terminal configuration,
population, spatial core count, transported original-tag count, nonempty
jam, and the initial full-lane event. Five exact rational densities per
shape test the finite initial-law integration, including `p=0` and `p=1`.
The older `check_path_core.py` remains the broader path-mass census.

Targeted controls distinguish colored and labeled periods (3×3 code 14),
later core growth, partial freezing without jam (2×2 code 13), and the
`N`-edge versus `N`-vertex cutoff. Unequal-population mixtures distinguish
`E[Z/N]` from `E[Z]/E[N]`. Positive-weight empty boards, repeated support,
and zero weights test the normalization conventions.

```sh
cd formal/lean
lake build
lake env lean Audit.lean
lake env lean StoppedCoreAudit.lean
cd ../..
python -m pytest -q
python scripts/check_stopped_core.py --report .artifacts/stopped-core.json
```

The replay records the exact local commit, tree, worktree status, source
hashes, executable hash, and output hash before and after verification.
Source changes during a run invalidate its provenance even if every
numerical comparison passed.

## 6. The remaining mathematical obligation

The needed large-torus estimate is still the
[late core-mass target](2026-11-19-maximal-core-and-path-mass.md#6-verification-boundary-and-the-next-estimate):
for some interval of fixed positive densities, prove

\[
 \lim_{L\to\infty}\lim_{t\to\infty}
 \mathbb E_p\!\left[\frac{|K(F^t(s))|}{N(s)};N(s)>0\right]=0.
\]

The initial iid full-lane estimate and its decay, the weaker sufficient
short-path estimate, and the population envelope retain their existing
prose scope. This increment proves the deterministic count identification
and exact finite-weight reduction. It supplies no estimate forcing the
limiting frozen fraction to vanish and makes no exchange of the two limits.
