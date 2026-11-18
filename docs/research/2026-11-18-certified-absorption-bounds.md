# Certified bounds for eventual gridlock

**Research increment — 18 November 2026. No novelty claim.**

The primary target is a fixed-positive-density statement about **eventual**
CLASSIC gridlock, followed by the stronger question of a positive sharp
transition. The [probability note](2026-11-18-probabilistic-gridlock-bounds.md)
defines those limiting claims. Main at
[`ce01a8b`](https://github.com/larsbx/traffic-theory-research/commit/ce01a8b38a6dea588653e1852633901fea9cf81a)
already includes PR #14's early-formation estimates and PR #12's CLASSIC
sparse-flow blueprint. Their finite-time and shrinking-density statements
leave the all-time, fixed-density estimate open.

The combined revision also includes main's
[`b5ebc5b`](https://github.com/larsbx/traffic-theory-research/commit/b5ebc5b411eb8ca8d7f4964931603b085d21b7cc)
tagged-fixation theorem from PR #16. Its
[exact event identity and Palm comparison](2026-11-18-tagged-fixation-and-gridlock.md)
connect eventual gridlock to eventual stopping of original cars, up to the
initial full-lane event. They do not supply the missing fixed-density estimate.

This increment makes a finite computation produce rigorous bounds on an
eventual event. The Lean layer proves the soundness of the actual CLASSIC
cutoff classifier and finite weighted bounds. Separate Python and Quint
implementations supply executable certificates and replay evidence. The
[relaxation note](2026-11-18-relaxation-obstructions.md) supplies a logarithmic
settling-time obstruction, counterexamples to two proposed shortcuts, and a
weaker expected-defect criterion. None of these establishes a positive
critical density.

## 1. Resolve a trajectory only when there is a certificate

Let \(F\) be the complete east-then-north CLASSIC update. A target state is
a **nonempty jam**. For an initial state \(s\) and nonnegative integer cutoff
\(T\), the probe has exactly three outcomes:

| Verdict | Checked evidence | Universal consequence |
| --- | --- | --- |
| `hit` | \(F^T(s)\) is a nonempty jam. | The initial state eventually jams. |
| `safe` | The terminal state is not a jam and equals \(F^a(s)\) for some \(a<T\). | No state on this initial trajectory ever jams. |
| `unresolved` | Neither certificate has been found at this cutoff. | The trajectory is retained in the uncertainty term. |

A safe orbit may have intermediate, submaximal movement. The result says
that it avoids complete gridlock; it does not say that it eventually reaches
full speed. At cutoff zero, an initial jam is a hit, but a nonjam state has
no earlier recurrence to certify. The empty fixed state becomes safe at
cutoff one and is never mislabeled as a jam.

The all-time claim follows from absorption and determinism. A repeated
non-target state lies on a positive-period cycle. If that cycle ever entered
an absorbing target, it could not return to its non-target starting point.
An earlier target in the initial prefix is likewise impossible because it
would persist to the non-target recurrent state. This proof does not assume
a maximum preperiod or rely on the empirical absence of future blockage.

[BML/Absorption.lean](../../formal/lean/BML/Absorption.lean) proves the general
absorbing-target theorem and instantiates it with the actual torus kernel.
The required concrete results are `absorptionProbe_hit_sound`,
`absorptionProbe_safe_sound`, and `absorptionProbe_mass_bounds`.
`jamCheck_iff` connects the executable predicate to semantic CLASSIC `Jam`.
The existing fixed-point equivalence is used only under CLASSIC; substituting
TRAIN would incorrectly count rotating homogeneous rings as jams.

The module also proves the earlier conditional safe-set reduction. Any
predicate \(U\) that is forward invariant under the actual update and
disjoint from the absorbing target gives an all-time avoidance certificate
whenever \(F^T(s)\in U\). The recurrence checker is one concrete executable
way to supply safe evidence, with no conjectured invariant region assumed.

## 2. Exact initial mass gives an interval for the eventual event

Write \(H_T,S_T,U_T\) for the sets assigned hit, safe and unresolved. Under
any initial probability law \(\mu\), let

\[
h_T=\mu(H_T),\qquad s_T=\mu(S_T),\qquad u_T=\mu(U_T).
\]

They partition the initial states, and the soundness theorem gives

\[
\boxed{h_T\le\Pr_\mu(\text{eventual jam})
       \le h_T+u_T=1-s_T.}
\tag{1}
\]

The interval width is exactly the unresolved initial mass. Increasing the
cutoff cannot invalidate a hit or a safe recurrence, so \(h_T\) is
nondecreasing, \(s_T\) is nondecreasing, and \(u_T\) is nonincreasing.
The intervals are nested. Zero unresolved mass makes the result exact.
These are universal finite-weight theorems, not statistical confidence
intervals or estimates based on a sampled proportion of outcomes.

The Lean statement uses any finite list of initial states and nonnegative
integer weights. It proves the inequalities, the three-way mass partition,
monotone refinement and exactness at zero unresolved weight. Its semantic
eventual-target predicate is noncomputable only in theorem statements; the
executable probe never calls a future-event oracle. A probability statement
for the entire initial space requires complete initial support, or explicit
accounting for all omitted mass.

### The symmetric iid law stays at time zero

For \(A=WH\) sites and exact rational \(p=a/b\), an initial complete board
with \(m\) cars has weight

\[
(p/2)^m(1-p)^{A-m}
=\frac{a^m[2(b-a)]^{A-m}}{(2b)^A}.
\tag{2}
\]

Thus a common positive denominator turns the initial iid integration into
the natural-number setting of the Lean mass theorem. There are
\(\binom Am2^m\) colored boards with \(m\) cars, and the binomial theorem
gives total numerator \((2b)^A\). The Python acceptance gate checks this
integer normalization as well as independent `Fraction` integration. This
probability-law calculation and normalization explanation are separate from
the current Lean probability-library scope; no general measure-theory or
analytic limit theorem is claimed.

If distinct initial boards coalesce into the same later board, they keep
their separate initial weights. If the same initial board is supplied twice,
the certificate integration rejects the duplicate. Reweighting a later state
as a fresh independent sample would compute a different law.

### Partial certificates remain valid without complete enumeration

The Python function `partial_probability_bounds` verifies a supplied set of
distinct complete initial-board certificates. Let \(h\) and \(s\) be the
initial masses of its accepted hit and safe certificates. Then

\[
h\le\Pr_\mu(\text{eventual jam})\le1-s.
\tag{3}
\]

Its uncertainty \(1-h-s\) includes both observed unresolved trajectories
and every omitted initial board. For example, at \(p=1/2\) on \(2\times2\),
certifying only the empty board as safe establishes the interval
\([0,15/16]\): that initial board has probability \(1/16\). It does not
establish zero gridlock probability for the other boards.

Each public `TraceCertificate` stores dimensions, the exact cutoff, every
complete state from time zero through that cutoff, a verdict, and a recurrence
index when safe. The verifier checks every transition against the production
CLASSIC kernel, code ranges, the full trace length, and the terminal evidence.
Individual certificates use Python integers, including boards too large for
64-bit ternary codes. Complete census operations have a separate explicit
size cap.

## 3. A finite result that exposes the cutoff problem

On the complete \(3\times3\) state space, the new classifier gives the
following exact initial-law intervals at \(p=1/2\). These are finite
enumeration results, not an extrapolation to large tori.

| Cutoff in complete rounds | Hit states | Safe states | Unresolved states | Lower probability | Upper probability |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 1,685 | 0 | 17,998 | \(775/32768\) | \(1\) |
| 4 | 4,952 | 3,139 | 11,592 | \(10525/131072\) | \(45821/65536\) |
| 8 | 5,861 | 10,978 | 2,844 | \(12433/131072\) | \(25213/131072\) |
| 16 | 5,951 | 13,660 | 72 | \(12613/131072\) | \(12901/131072\) |
| 32 | 5,951 | 13,732 | 0 | \(12613/131072\) | \(12613/131072\) |

Cutoff 16 has unresolved probability \(9/4096\), even though most initial
states are classified. Cutoff 32 closes the interval, giving

\[
q_3(1/2)=\frac{12613}{131072}.
\tag{4}
\]

The independent existing full-graph classifier agrees. Of the 13,732 safe
initial states, 11,700 reach an intermediate cycle and 2,032 reach full flow,
including the empty configuration. This is why safe recurrence is a broader
certificate than eventual full speed.

The complete \(3\times3\) census is Python evidence. The additional
Lean/Quint replay selects exactly the 72 states unresolved at cutoff 16 and
checks them at both cutoffs 16 and 32. It does not relabel those 144 rows as
a three-language exhaustive \(3\times3\) census.

## 4. Execution is connected to the proved kernel

The fast Lean evaluator uses a data-valued `MaterializedBoard`, rather than
repeatedly constructing nested configuration functions. The following kernel
proofs connect it to the original update:

- `boardConfig_materialize`: reading a materialized board recovers the original
  configuration.
- `boardConfig_step` and `boardConfig_iterate`: materialized steps and all
  their iterates agree with the actual CLASSIC torus update.
- `absorptionProbe_eq`: the executable materialized probe has exactly the
  original kernel contract's verdict.

This representation change improves evaluation without introducing a trusted
replacement transition or weakening the theorem. The exporter calls the
proved probe and reports the original code, cutoff, terminal code, verdict
and initial population.

[Absorption.qnt](../../formal/quint/Absorption.qnt) independently builds its
finite orbit using the existing actual Quint BML kernel. Its internal flag
checks legal raw states and east-phase intermediates, species conservation,
every transition link, movement bounds, blockage/fixed-state equivalence and
jam persistence. The adapter requires that flag before exposing a row;
ternary encoding alone cannot validate an illegal raw state.

The default [acceptance gate](../../scripts/check_absorption.py) covers:

| Evidence | Exact scope |
| --- | --- |
| Universal Lean proofs | Arbitrary cutoffs and initial states, arbitrary finite initial Nat weights; actual CLASSIC instantiation and materialized refinement. |
| Lean/Quint/Python cutoff replay | All 3,720 initial boards on all 14 positive ordered rectangles with \(WH\le6\), at cutoffs 0, 1, 2, 4, 8 and 16: 22,320 rows. |
| Additional targeted \(3\times3\) replay | 72 initially unresolved boards at cutoffs 16 and 32: 144 rows. |
| Additional larger witnesses | 10 rows covering a late jam, an intermediate recurrent orbit, and the vacant-cut-to-jam counterexample. |
| Exact probability integration | Every population coefficient is recomputed from the verified verdict arrays, and initial populations match the independent oracle. Seven rational densities per exhaustive rectangle/cutoff are checked against initial integer weights and the full-graph oracle; a complete 19,683-state Python \(3\times3\) census runs through cutoff 32. |
| Rejection controls | 14 certificate/protocol/aggregation mutations, including empty-as-jam, unresolved-as-safe, wrong recurrence, wrong phase count, altered transitions, duplicate initial probability, wrong initial populations, wrong probability coefficients and missing output. Omitted probability is also explicitly checked. |

Quint parsing, typechecking and its deterministic tests run through the
pinned 0.33.1 TypeScript interpreter. Its tests include 10 new absorption
cases and 10 imported BML cases. This is not an Apalache or unbounded temporal
model-checking result. Cross-language agreement remains finite evidence; the
universal theorem belongs to the Lean implementation.

The gate builds the Lean exporter before use, audits the BML declarations and
exporter, and records source hashes before and after execution plus the exact
binary hash. The only permitted proof axioms remain `propext`, `Quot.sound`
and `Classical.choice`. A source inventory, compiled workflow or queued hosted
job does not substitute for a successful receipt on the revision being claimed.

From the repository root, after installing the pinned tools and dependencies:

```sh
python -m pytest -q tests/test_absorption.py tests/test_obstructions.py
python scripts/check_absorption.py --report .artifacts/absorption-acceptance.json
```

The hosted jobs run the same gate with `--backend lean` and `--backend quint`
separately. The implementation does not yet prove completeness of the old
pointer-doubling classifier or a universal finite cutoff for this new probe.
Zero unresolved mass suffices for each exact finite result advertised here.

## 5. What would close the positive-density part of the target?

There are now two explicit sufficient routes, with different missing estimates.

**Certified initial-mass route.** At a fixed positive density, construct
cutoffs \(T_L\) or more general verified safe certificates such that the
total upper bound in (1) or (3) tends to zero as \(L\to\infty\). In the
cutoff form this requires both \(h_{T_L}\to0\) and \(u_{T_L}\to0\).
A small observed jam fraction with a large unresolved mass does not suffice.
Nor does exact closure on finitely many small tori establish a size-uniform
bound. A useful next construction should compress large sets of initial
states or prove an invariant with a controllable initial-law preimage.

**Late expected-defect route.** The accompanying
[relaxation note](2026-11-18-relaxation-obstructions.md#5-a-weaker-sufficient-target-late-expected-defect-density)
defines the raw HBK defect \(V\), proves that every jam satisfies
\(m\le2V\), and obtains, for \(p>0\),

\[
q_L(p)\le e^{-pL^2/8}
 +\frac4{pL^2}\liminf_{t\to\infty}
      \mathbb E_{\mu_{L,p}}[V(F^t(s))].
\tag{5}
\]

Thus late expected defect density tending to zero would imply nonjamming
with high probability, even if the remaining defects are not identically
zero. The time limit here is taken for each fixed \(L\) before the size
limit. One small value at a selected cutoff cannot replace it: the note
gives a four-car example on every \(L\ge4\) where \(V\) increases.
The missing estimate is still

\[
\liminf_{t\to\infty}\mathbb E_{\mu_{L,p}}[V(F^t(s))]=o(L^2)
\quad\text{at fixed }p>0.
\]

The same note rules out using a fixed burn-in to reach the full-flow zero
set with high probability, and exhibits an initial winding vacant cut that
becomes a jam in one round. Those counterexamples identify extra conditions
that any proposed invariant or drift proof must supply.

These results make the remaining target precise and checkable. They do not
prove a positive nonjamming interval, equality of the limiting threshold
endpoints, or a numerical critical density. No claim of closing those open
questions is made.
