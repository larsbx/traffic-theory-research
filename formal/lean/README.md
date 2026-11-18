# Lean finite-torus kernel

This dependency-free package pins **Lean 4.34.1** and formalizes synchronous BML
updates: east cars move simultaneously from the pre-east state, then north cars
move simultaneously from the resulting state. Both torus dimensions must be
positive. Singleton dimensions are included.

## Run

```sh
cd formal/lean
lake build
lake env lean Audit.lean
.lake/build/bin/bml_replay 3 3
```

`bml_replay WIDTH HEIGHT` enumerates all `3^(WIDTH*HEIGHT)` states. Its headerless
CSV columns are:

```text
index,east_state,next_state,east_moves,north_moves
```

State codes use `0 = empty`, `1 = east`, `2 = north`, with digit position
`x + WIDTH*y`, exactly as in `bml.exhaustive`. The executable calls the same
`halfStep`, finite-torus directions, and movement predicate used in the proofs.
It does not embed Python-produced expected transitions.

## Kernel-checked coverage

| Module | Results |
|---|---|
| `BML/Kernel.lean` | Moving sources empty and destinations fill; other species remain in place; a half-step is fixed iff its cars are blocked; a full east-then-north step is fixed iff both local blocking conditions hold; equivalence with no movement in either phase; frozen-state persistence, including after a transient; full occupancy freezes; the empty state is fixed but is not a jam. |
| `BML/Transport.lean` | Explicit bijection between each species' cars before and after its phase: survival, injectivity, and surjectivity. Nonemptiness is preserved by a full step and every iterate. |
| `BML/Torus.lean` | Positive finite cyclic coordinates with proved inverse shifts; the general kernel is instantiated on `Fin WIDTH × Fin HEIGHT`; executable base-three encoding, decoding, and counts. |
| `BML/Counting.lean` | The position enumeration is complete and has no duplicates. Filtered species lists agree with the executable `speciesCount` sums; the occupied-list length is their sum. Transport induces a list permutation, proving numerical species conservation under every half-step, and total-count conservation under every full-step iterate. |
| `BML/FiniteCycle.lean` | Every endofunction on a nonempty finite closed carrier has a positive simple cycle bounded by the carrier's length. The proof uses pigeonhole reasoning and a minimal positive return time. |
| `BML/Blocking.lean` | A frozen state's blocker map preserves occupancy. An actual blocker walk lifts to nonnegative east/north displacements and seam-crossing counts. Closure implies divisibility by the torus side lengths, hence the shorter-side lower bound. |
| `BML/Extremal.lean` | Full east rows and full north columns are nonempty frozen states with exactly WIDTH and HEIGHT cars. Choosing the shorter line attains `min(WIDTH, HEIGHT)`. |
| `BML/Gridlock.lean` | Every jam has a simple occupied blocker cycle of length between `min(WIDTH, HEIGHT)` and its actual car count. This proves the G1 lower bound, the exact minimum jam budget, and that fewer cars never reach a jam at any iterate. |
| `BML/Arithmetic.lean` | Divisibility of positive winding lengths implies the `min(WIDTH, HEIGHT)` lower bound. The proposed class packing expression simplifies to `floor(2*g/3)` and attains exact `2/3` iff `3` divides `g`. These are arithmetic components of G1 and F. |
| `BML/Witnesses.lean` | A stronger nonmonotonicity example on width 4, height 2. State `3858` reaches jam `2048` after three steps. Adding one north car at `(0,0)` yields `3860 ↔ 4340`, which never jams. The added car remains blocked forever. An explicitly tracked original north car moves at every step. |

The full-step fixed-point converse does not assume that two consecutive updates
cannot cancel. It proves that a moved east car leaves its source empty, and the
north phase cannot restore an east car there. The east phase must therefore
already be fixed; the north condition follows.

`Jam` explicitly requires a nonempty state. In particular, the empty state is not
a counterexample to the classification convention that assigns it free flow.

The minimum-gridlock proof connects three independently checked statements:
the occupied-position list is closed under the blocker map; finite cycle
extraction supplies distinct occupied vertices; and the actual east/north walk
closes only after a positive winding of at least the shorter side. Thus

```text
min(WIDTH, HEIGHT) ≤ cycle length ≤ carCount
carCount = speciesCount east + speciesCount north
```

`few_cars_never_jam` then uses numerical conservation to apply this bound at
every future time. It does not assert eventual speed one or formalize the
positive-asymptotic-velocity consequence. `exists_jam_at_most_iff` proves that
a jam within a budget of `n` cars exists iff `min(WIDTH, HEIGHT) ≤ n`; the
construction with every exact larger car count is still a separate obligation.

The strong witness's `originalTrace` is an identity-following recurrence using
`transport`, rather than a statement that some unlabeled car moves. The tracked
car occupies column 1 in both cycle states and was present before the added car.

## Audit and trust boundary

`Audit.lean` traverses every `BML` declaration and its transitive axiom
dependencies. It checks that the required theorem names are present and rejects
any axiom outside Lean's usual `propext`, `Quot.sound`, and `Classical.choice`.
Thus incomplete proofs and native decision-result axioms fail the audit.
Concrete witness proofs use kernel-reduced `decide`, and the infinite-time
claims use induction.

The replay executable provides finite comparison evidence against the Python
and Quint implementations. Such comparisons are not an all-size source
refinement proof. The numerical counting identities and conservation have
general Lean proofs; unrestricted encoding correctness and cross-language
source correspondence remain separate obligations.

## Remaining obligations

This package does **not** prove the full list G0–F. The missing general
mathematics remains:

- Extend G1's proved lower bound and minimum attainment to frozen constructions
  at every exact count between the minimum and full occupancy.
- Formalize the G2 non-gridlocking configurations for every sub-full car count.
- Prove the subgroup/coset assertion and both directions of rigidity Lemma R.
- Connect Lemma R to the cyclic class packing upper bound and all densest
  constructions in F.
- Formalize eventual periodicity/classifier correctness and unrestricted
  Python-to-Lean source correspondence.

No probabilistic critical density, asymptotic typical-case theorem, or
quasicrystal spectral statement is asserted by this layer.
