# B7.6: inclusive sparse flow in the actual CLASSIC kernel

## Review basis and result

This change starts from [PR #32](https://github.com/larsbx/traffic-theory-research/pull/32)
at `6ac0624afdfea9c7e9d65d7884dbe2cef4e64a40`. It closes blueprint B7.6
in Lean, extending the existing strict sparse-flow theorems to
`2 * carCount ≤ gcd(W,H)`. The preparation is local for review; it does not
publish a branch, update the PR, or merge anything.

The two mathematical source files are
[`SparseDynamics.lean`](../../formal/lean/BML/SparseDynamics.lean) and
[`SparseSpeed.lean`](../../formal/lean/BML/SparseSpeed.lean). The definition of
`torusStep`, the species phases, `CanMove`, transport, and counting are unchanged.

For positive side lengths, put

\[
g=\gcd(W,H),\qquad m=\operatorname{carCount}(s),\qquad
K=m\max(g-2,0),\qquad D=\operatorname{lcm}(W,H)K.
\]

Under `2m ≤ g`, the formal development proves:

1. Every original car is blocked at most `g−2` times in every finite prefix.
2. Every finite prefix contains at most `K` rounds with any blocked car.
3. The actual orbit is `StaticFree` at time `D`.
4. Every full round at every `t ≥ D` moves every car in its species phase.

Subtraction is Lean's truncated natural subtraction. The empty board is
included, with `D = 0`. When `g = 2`, at most one car is admitted, also with
deadline zero. For odd `g`, integral populations make the inclusive and
strict admitted populations identical; the additional populations occur at
even `g`.

All times count **complete east-then-north rounds**. In the original
traffic-light convention, one such round comprises two half-steps. The
statement does not claim the upper bound is sharp.

## Formal theorem interfaces

The existing public theorem names now take the inclusive population proof.
With `hw : 0 < w` and `hh : 0 < h`, the deadline declaration is:

```lean
theorem low_density_speed_one_deadline (s : Config (Position w h))
    (hm : 2 * carCount w h s ≤ Nat.gcd w h)
    (t : Nat) (ht : sparseSpeedDeadline w h s ≤ t) :
    AllMove (eastDirection w h hw) (northDirection w h hh)
      (iterate (torusStep w h hw hh) t s)
```

The associated declarations are `low_density_tag_block_bound`,
`low_density_block_bound`, `low_density_staticFree_deadline`,
`low_density_square_speed_one_deadline`, and `low_density_speed_one`.
The tag theorem additionally requires `s p = sp.cell`, so it counts the
blocks of an actual original car of the specified species.

The square specialization has deadline `n * m * (n−2)` under `2m ≤ n`.
`staticFree_of_blockedRoundCount_bound` remains a reusable theorem accepting
any uniform blocked-round budget; it has no sparsity assumption.

## Equality proof and the transition into free flow

### Exact saturation

`CorrectedAlternating` asserts both:

- a corrected class is occupied exactly when its successor is vacant;
- two occupied sites with the same corrected class are the same site.

Let `xs` be the list obtained by mapping the actual occupied cells to their
corrected classes. If no adjacent pair is empty, then
`xs ++ xs.map cyclicPrev` covers all `g` classes. Its length is `2m ≤ g`.
A finite-list permutation argument forces this cover to have no repetition.
Disjointness of the two halves rules out adjacent occupied classes;
injectivity of the first half gives singleton occupancy. This proves
`corrected_alternating_of_no_emptyPair`. In particular the no-pair case
cannot occur under strict sparsity; it forces equality.

### Actual two-phase movement

`corrected_alternating_allMove` proves actual `CanMove` conditions.
An east car has a vacant next corrected class. A north car also has a
vacant target before the round, but that alone is insufficient: the east
phase might fill the target. The potential east source would occupy the
north car's corrected class. Singleton occupancy rules that source out.
Thus north eligibility holds on the actual post-east configuration.

This argument uses the same target-class geometry as `corrected_release`;
it does not incorrectly promote that lemma's existential surviving occupant
into movement of every car without the singleton proof.

`corrected_no_emptyPair_step` is the contrapositive of the existing
backwards empty-pair theorem. Combined with conservation and saturation,
it gives `corrected_alternating_step`. Induction gives
`corrected_no_emptyPair_perpetual_allMove` for every subsequent round.
One fully moving round alone is never used as a permanence criterion.

### Accounting for the final blocked round

The existing B7.5 rank argument is factored into a private helper: if an
original tag avoids a fixed corrected class through time `T`, rotating
that class to zero gives a rank in `1,…,g−1`. Each blocked round decreases
the rank by one; each successful move preserves it. The number of blocks
is consequently at most `g−2`.

The inclusive theorem uses induction on prefix length. If an empty pair
exists at time `T`, its first class was empty at every earlier time and
remains empty at `T+1`. Indeed, a tag reaching that class would either have
moved from the same class or been blocked in its successor, both vacant at
`T`. The rank argument therefore covers the transition round even if the
empty pair disappears at its end. There is no additional `+1` in the bound.
If there is no pair at `T`, the next round moves every tag, adding zero
to the count.

Summing the tag bounds gives `K`. If the state at time `D` were not
static-free, persistence of static-free states would imply that each of
the `K+1` preceding-or-starting windows of length `lcm(W,H)` was not
static-free. The existing finite-window theorem then supplies a blocked
round in each disjoint window, contradicting the uniform budget. This
establishes both the deadline and all later movement.

## Assumptions, dependencies, and compatibility

| Item | Scope |
| --- | --- |
| Dimensions | Positive natural `w,h`; singleton dimensions are included. |
| Population | Total actual car count, with `2m ≤ gcd(w,h)`. |
| Configuration | Arbitrary deterministic initial arrangement; no distribution or species balance. |
| Update | Simultaneous east phase, then simultaneous north phase; destinations tested in each phase's input state. |
| Original cars | `carTrace`, its preservation and surjectivity, and `RoundCanMove`. |
| Geometry | Existing corrected classes, cyclic shifts, and finite free-flow/lcm results. |
| External theorem assumptions | None. The literature is attribution and a model comparison, not an imported axiom. |
| Lean/package dependencies | Lean 4.34.1 unchanged; no new external package or lockfile/toolchain change. |
| Added module import | Existing `BML.Rigid`, used for `AllMove` in `SparseDynamics`. |
| Transitive proof axioms | Only `propext`, `Quot.sound`, and `Classical.choice`. |
| Public interface change | The same `low_density_*` names now accept `≤`; callers holding a `<` proof can pass `Nat.le_of_lt` of it. |
| Replay interface change | Schema advances from `bml.sparse-speed-replay.v2` to `.v3`; the certified-domain flag and deadline now include equality. |

The general audit explicitly requires the six new public dynamics theorems
to be theorem declarations, and checks their transitive axiom dependencies.
The proof uses neither `sorry` nor native decision-result axioms.

## Literature and attribution

[Kozlov–Tatashev–Yashina, arXiv:2310.02291v1](https://arxiv.org/pdf/2310.02291)
is a **2023 preprint**. Theorem 1 already includes the rectangular inclusive
gcd threshold and alternating equality argument. Sections 1–2 specify ECA184
and ordered type phases; `q = 0` fixes types. These stated rules match the
CLASSIC vacancy test at the source-description level. The proof here checks
the repository's kernel directly.

The related **published** paper is by **M. V. Yashina and A. G. Tatashev**,
*Mathematical Methods in the Applied Sciences* 47 (2024), 14341–14352,
[DOI 10.1002/mma.10276](https://doi.org/10.1002/mma.10276).
Its publisher abstract confirms the inclusive threshold; full journal text
was not available in the retrieval used. The three-author preprint and
two-author journal citation are kept distinct.

The [original BML Model I](https://arxiv.org/pdf/cond-mat/9206001), pp.2–3,
explicitly forbids following into a site vacated during the same species
phase. This supports the CLASSIC/queue distinction used in the controls.
The contribution claimed here is machine-checked coverage and explicit
kernel-derived bounds, not a new inclusive threshold or a priority claim
for stabilization estimates.

## Verification and finite scope

Local checks completed during preparation:

| Check | Result |
| --- | --- |
| `lake build` | Passed, 173 build jobs. |
| `lake env lean Audit.lean` | Passed: 1,716 declarations, 1,279 theorems; only the three standard axioms above. |
| `lake env lean SparseSpeedAudit.lean` | Passed: 10 exporter declarations, concrete equality proof terms, zero-deadline single-car case, and boundary controls. |
| `python scripts/check_sparse_speed.py` | Passed: 75,716 boards, including 61,608 equality boards, and 15 targeted cases. |
| `python -m pytest -q tests/test_iid.py tests/test_blueprint.py` | Passed: 480 tests, including both resolved derivative-certificate regressions. |
| `python -m pytest -q` | Passed: 1,746 tests across the complete Python suite. |
| `git diff --check` | Passed. |

The sparse replay enumerates every admitted population, placement, and
species assignment on these 16 ordered shapes:
`1×1, 1×5, 5×1, 2×2, 2×4, 4×2, 3×3, 3×6, 6×3, 4×4, 4×8, 8×4,
5×5, 5×10, 10×5, 6×6`.
It compares the compiled Lean exporter with an independent scalar CLASSIC
implementation for 592,319 rounds through first recurrence, including
58,232 alternating-invariant checks. Of the equality boards, 27,872 have
at least one blocked round. The latest permanent-flow entry in this finite
domain is round 11; the largest theorem deadline in it is 72.

| Control | Observed result |
| --- | --- |
| 4×4, code 19: alternating two-car equality | Permanent movement from time zero. |
| 4×4, code 4: adjacent two-car equality queue | One blocked round, then permanent movement from time 1. |
| 6×12 and 12×6, three-car equality queues | Two blocked rounds, permanent movement from time 2; deadline 144. |
| 2×2 with two cars | Two tested blocked rounds exceed the would-be budget zero; no deadline certified. |
| 3×3 with two cars | Four tested blocked rounds exceed the would-be budget two; no deadline certified. |
| 4×4 with three cars | Eight tested blocked rounds exceed the would-be budget six; no deadline certified. |
| 5×10, code 487 | One block occurs at round 9; permanent entry 10 exceeds the block budget 6, while satisfying elapsed deadline 60. |
| Movement mutations | TRAIN queue motion and a north phase incorrectly reading the pre-east board disagree with the CLASSIC traces. |

The above-boundary controls need only finite prefixes to refute the
out-of-domain budgets. They are not reported as full-orbit certifications.
Finite replays supplement the universal Lean proof; they are not an
unrestricted Python/Lean refinement theorem or a fresh enumeration of all
25-cell configurations from PR #32.

## Exact-head hosted status and resolved reviews

At the inspected PR head `6ac0624afdfea9c7e9d65d7884dbe2cef4e64a40`,
all three hosted workflows and all five checks were **queued**, with no
conclusion:

- [Finite BML acceptance, run 44933122238](https://github.com/larsbx/traffic-theory-research/actions/runs/44933122238)
- [TRAIN acceptance, run 44933122187](https://github.com/larsbx/traffic-theory-research/actions/runs/44933122187)
- [Formal acceptance, run 44933122382](https://github.com/larsbx/traffic-theory-research/actions/runs/44933122382)

This supplies no hosted acceptance for the prepared local changes.
GitHub reports both derivative-certificate review threads resolved. Source
inspection confirms the endpoint-positive test and the constant-function
`None` return, with the corresponding regression cases in `tests/test_iid.py`.
Those findings are **resolved history**, not outstanding blockers.

Reproduce the relevant local gates after checking out the reviewed change:

```sh
cd formal/lean
lake build
lake env lean Audit.lean
lake env lean SparseSpeedAudit.lean
cd ../..
python scripts/check_sparse_speed.py --report .artifacts/sparse-speed-inclusive.json
python -m pytest -q
git diff --check
```

The generated replay report records the exact local revision, tree,
worktree cleanliness, exporter SHA-256, and ordered-trace SHA-256. These
bind the finite replay to the reviewed source without claiming that hosted
CI has completed.
