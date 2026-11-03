# NT-CIRCLE-v2 progress and handoff

Goal 1 complete. Goal 2 is incomplete; goals 3–5 have not been started. No circle discrepancy, annulus count,
`estcross`, B-process, or improved exponent-pair theorem is claimed.
The earlier numerical obstruction and handoff remain valid.

## Files and exact exports (goal 1)

All exports below are in `WaveTurbulence.NumberTheory` unless specified.
The exact Lean statements, including every endpoint, are in the named files.

- `ExponentialSums.lean`: public toolkit entry point, with no root import edit.
- `Sawtooth.lean`: exposed `sawtooth x = Int.fract x - 1/2`, periodicity,
  integer values, oddness away from integers, and `|sawtooth x| <= 1/2`.
- `Phase.lean`: exposed `expPhase x = exp(2*pi*i*x)`, phase identities,
  unit norm, and the reciprocal weight used in Kusmin–Landau.
- `IntegerDistance.lean`: exposed
  `integerDistance x y = |x-y-round(x-y)|`, its minimizing property,
  zero characterization, symmetry, triangle inequality, and integer invariance.
- `SineSeries.lean`: Abel bounds and
  `SineSeries.tendsto_sum_sin_div_nat`:
  for 0<x<1, `sum_{n<N} sin(2*pi*x*n)/n -> pi*(1/2-x)`.
  This proof is independent of zeta-function assumptions.
- `SawtoothFourier.lean`: exposed two-sided Fourier polynomial
  `sawtoothFourier K theta = -sum_{0<|m|<=K} expPhase(m*theta)/(2*pi*i*m)`;
  exact defect `sawtoothRem`; and majorant equal to one on integers and to
  `min(1/(K*integerDistance theta 0),1)` otherwise. Main result
  `norm_sawtoothRem_le` proves, for K>=1 and every theta,
  `norm(sawtoothRem K theta) <= (5/2)*sawtoothMajorant K theta`.
  The sharper noninteger remainder bound is
  `1/(pi*(K+1)*integerDistance theta 0)`.
- `KusminLandau.lean`: `kusmin_landau_discrete` gives constant **one**:
  `norm(sum_{a<n<=b} expPhase(f n)) <= 1/delta` if 0<delta<=1/2 and the
  increasing consecutive differences stay in one fixed strip
  `[m+delta,m+1-delta]`. Merely bounding their fractional parts is not assumed
  sufficient. The final increment at b is included explicitly.
- `SecondDifference.lean`: `van_der_corput_second_difference` gives
  `norm(sum_{a<n<=b} expPhase(f n)) <= 8*(c*(b-a)*sqrt(lam)+1/sqrt(lam))`
  for a<=b, lam>0, c>=1, and consecutive second differences in `[lam,c*lam]`.
  The window counting, strip partition, and floor-error terms are proved.
- `DerivativeTests.lean`: the actual continuous versions `kusmin_landau`,
  `kusmin_landau_of_antitone`, `van_der_corput_second_derivative`, and
  `van_der_corput_second_derivative_of_neg`. They assume real derivatives
  only on `[a+1,b+1]`, with the same constants. Both first-derivative
  monotonicities and both second-derivative signs are covered. Unit and
  second-unit increment bounds are proved using mean value theorems,
  so the discrete estimates are not substituted for unproved continuous tests.
- `Differencing.lean`: finite Cauchy–Schwarz and finite-group Weyl differencing.
- `WeylDifferencing.lean`: `weyl_vdC_sq` and `weyl_vdC_expSum` prove the
  integer-interval A-process with factor `(N+H)/(H+1)`, shifts `-H<=h<=H`,
  and exact overlaps `{n in (a,a+N] : n+h in (a,a+N]}`. They hold for all
  natural N,H, including zero. There is no assumed correlation bound.

## Approach, mining, and provenance

Searched Mathlib NumberTheory and Analysis, including PoissonSummation, and
mined KAM-dev, eth-constants, Frohlich-Spencer, Balaban, and DOZZ. Searches of
those repositories did not locate the oscillatory-sum tests. Mathlib has
Poisson summation but no matching Kusmin–Landau or truncation-error result.

Further public-source discovery located Jason Hickey's Apache-2.0 repository
[Salt](https://github.com/jyh/salt/tree/3d7274047aabeea823abf1c0bdf675ce165dbca2).
The checkout is in `/home/scott/wt-scratch/nt-circle/salt`, outside this repository.
Proofs were adapted from `ExpSum/Basic.lean`, `ExpSum/Kusmin.lean`,
`ExpSum/VdCorput2.lean`, `LS/Dist.lean`, `MR/Sawtooth.lean` sections 1,3,4,
and `Weil/Sawtooth.lean` S1. Copyright notices and the full `SALT-LICENSE`
are included. No Salt dependency, axiom, provider, or assumption package is
imported. These are local Lean proofs checked against the pinned Mathlib.

Port changes: module headers and public imports; exposure of meaningful
public definitions; one shared phase; narrow imports; current tactic names;
removal of obsolete campaign commentary and unused A-process hypotheses.
The continuous derivative-to-difference bridges, opposite-sign tests, canonical
sawtooth API, and finite-group differencing are new local proofs.

## Exact checks and output (goal 1)

Each compile ran sequentially through wt-throttled with default budgets.
Successful final focused builds, all without warnings:

    nice -n 5 lake build WaveTurbulence.Foundations.NumberTheory.SineSeries
    # Built ...SineSeries (4.9s); Build completed successfully (3527 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.NumberTheory.SawtoothFourier
    # Built ...SawtoothFourier (5.4s); Build completed successfully (3532 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.NumberTheory.SecondDifference
    # Built ...SecondDifference (8.6s); Build completed successfully (3257 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.NumberTheory.WeylDifferencing
    # Built ...Differencing (1.2s), ...WeylDifferencing (3.4s);
    # Build completed successfully (3261 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.NumberTheory.DerivativeTests
    # Built ...DerivativeTests (4.1s); Build completed successfully (3258 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.NumberTheory.ExponentialSums
    # Built ...ExponentialSums (3.5s); Build completed successfully (3540 jobs).

The job totals include cached dependency facets; only project modules were built.
An initial invalid import path produced a missing-file error, never a Mathlib
rebuild. Other port failures (public imports, renamed phase lemmas, cast
normalization, and explicit function arguments) were repaired before these checks.
No budget override or artifact deletion was used.

    nice -n 5 lake env lean /home/scott/wt-scratch/nt-circle/ToolkitAxioms.lean
    # exit 0; output saved to /home/scott/wt-scratch/nt-circle/toolkit-axioms.log

The axiom probe checks the three main definitions, the sine-series limit,
the Fourier identity and error bound, discrete and continuous derivative tests
(including decreasing/negative variants), integer-interval A-process, and
finite-group differencing. Every result reports exactly
`[propext, Classical.choice, Quot.sound]`. No custom axioms.

    python3 scripts/check_lean_modules.py --root . --files WaveTurbulence/Foundations/NumberTheory/*.lean --max-lines 1500
    # check_lean_modules: PASS (11 Lean files, 0 comparator configurations)
    git diff --check
    # exit 0, no output
    rg -n 'maxHeartbeats|sorry|axiom|admit|unsafe|opaque|set_option' WaveTurbulence/Foundations/NumberTheory --glob '*.lean'
    # exit 1, no matches

## Uncertainties, errata, deviations, remaining work

No new suspected defect in the pinned DH23 source beyond the previously reported
F31 issues. The toolkit chooses a classical pointwise Fourier remainder rather
than a Vaaler polynomial. Turning it into a sharp summed bound for circle arcs
is additional work; no Erdős–Turán or circle discrepancy estimate is inferred
without proving that step. Endpoints at integers are retained, not replaced by
the midpoint convention.

Goal 2 is next. Goals 3–5 have not been skipped or represented by conditional
statements. No changes to frozen files, shared APIs, root, manifest, or ledger.

## Goal 2: proved ingredients, not completion

After the goal-1 commit, the following additional modules were proved and
checked. The uniform disc discrepancy estimate remains open.

- `SawtoothSmoothing.lean`: exposed `periodicBernoulliTwo x =
  fract(x)^2-fract(x)+1/6`; pointwise lower and upper envelopes
  `(B(x+h)-B(x))/(2h)-h/2 <= psi(x) <= (B(x)-B(x-h))/(2h)+h/2`
  for every h>0, including integer x; and the absolutely convergent identity
  `HasSum (cos(2*pi*n*x)/n^2) (pi^2*B(x))` for every real x.
- `SmoothingFourier.lean`: proves summability and the unconditional bound

      |sum_i psi(f_i)| <= #s*h/2 +
        (sum'_{n>=0} |e(nh)-1| |sum_i e(n*f_i)| / n^2)/(2h*pi^2).

  The n=0 summand is zero. No exponential-sum bound is a premise. Both chord
  bounds `|e(x)-1| <= 2` and `|e(x)-1| <= 2*pi*|x|` are proved.
- `Counting/CircleArc.lean`: the two actual derivatives of the square-root
  circle height; curvature ratio eight on height blocks `[H,2H]`; and
  `circle_arc_exp_sum_le`, applying the continuous second-derivative theorem
  to a translated arc with arbitrary horizontal and vertical shifts. Its
  geometric height-block hypothesis does not assume an exponential estimate.
- `Counting/LatticeDisc.lean`: an actual finite enumeration on `Fin 2 -> Z`,
  `mem_latticeDisc` characterizing the closed Euclidean disc for every
  nonnegative radius and every center in `EuclideanSpace R (Fin 2)`, and an
  exact vertical-slicing formula. In that formula each column contributes
  `2*height - psi(c_1+height) - psi(height-c_1)`. No boundary points are dropped.
- `HalfPowerSums.lean`: finite head bound `sum_{i<H} 1/sqrt(i+1) <= 2sqrt(H)`
  and finite/infinite tail bounds `sum_{n>H} 1/(n*sqrt(n)) <= 2/sqrt(H)`, H>0.

Successful targeted checks, sequential through wt-throttled, without warnings:

    nice -n 5 lake build WaveTurbulence.Foundations.NumberTheory.SawtoothSmoothing
    # Built ...SawtoothSmoothing (4.7s); completed successfully (3671 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.NumberTheory.SmoothingFourier
    # Built ...SmoothingFourier (4.1s); completed successfully (3685 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.Counting.CircleArc
    # Built ...CircleArc (8.4s); completed successfully (3259 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.Counting.LatticeDisc
    # Built ...LatticeDisc (6.9s); completed successfully (3310 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.NumberTheory.HalfPowerSums
    # Built ...HalfPowerSums (4.4s); completed successfully (3137 jobs).

The source for the head half-power proof is identified in its module header;
the other goal-2 proofs are new local proofs using Mathlib. A scalar module
diamond in the circle derivative calculation was resolved with `using!`, as
in Mathlib's derivative API; no budget change or new instance was introduced.

The exact axiom check is
`nice -n 5 lake env lean /home/scott/wt-scratch/nt-circle/CircleIngredientsAxioms.lean`,
with output at `/home/scott/wt-scratch/nt-circle/circle-ingredients-axioms.log`.
It checks the disc characterization, slicing, arc estimate, smoothing envelopes,
Bernoulli series, summed smoothing bound, and all three half-power bounds.
Exit 0: all ten results report exactly `[propext, Classical.choice, Quot.sound]`.
Module checks pass for all 17 Lean files under the packet's owned directories;
`git diff --cached --check` is clean.

Remaining goal-2 work: combine the frequency head/tail estimates with the arc
bound, prove the global arc-block decomposition uniformly in the horizontal
center, and control the height-sum/area error. None is assumed in a purported
circle theorem. Goals 3–5 still remain open.

## Goal 2: quantitative block milestone

The frequency head/tail combination above is now proved, together with its
application to actual circular height blocks:

- `SmoothingBounds.lean` gives a distinctly named conditional Fourier
  inequality: an `A sqrt(n)` positive-frequency bound implies
  `|sum psi(f_i)| <= #s/(2K) + ((2*pi+2)/pi^2)*A*sqrt(K)`.
  The underlying majorant series is bounded by `(4*pi+4)*A/sqrt(K)`.
  These generic numerical lemmas are not circle theorems.
- `Counting/CircleSawtooth.lean` discharges that frequency premise for the
  actual translated arc, giving the displayed local bound with
  `A = 8*(8*(b-a)*sqrt(R^2/(8H^3)) + 1/sqrt(R^2/(8H^3)))`.
- `Counting/CircleBlockGeometry.lean` proves monotonicity on each semicircle
  and width bounds `4H^2/R` from actual geometric endpoint conditions.
- `Counting/CircleBlockBounds.lean` bounds the local amplitude by `160sqrt(H)`
  and optimizes the natural cutoff. Its main result
  `circle_left_block_sawtooth_sum_le_optimized` has radius `r^3`, height
  `r^2 <= H <= r^3`, arbitrary translations, and conclusion `|sum psi| <= 322H/r`.
  It assumes a genuine height block on the full real interval required by
  the derivative test. No exponential or sawtooth estimate is a premise.

Final targeted builds, all warning-free:

    nice -n 5 lake build WaveTurbulence.Foundations.Counting.CircleSawtooth
    # Built ...SmoothingBounds (4.9s), ...CircleSawtooth (3.7s).
    nice -n 5 lake build WaveTurbulence.Foundations.Counting.CircleBlockGeometry
    # Built ...CircleBlockGeometry (2.6s); completed successfully (3260 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.Counting.CircleBlockBounds
    # Built ...CircleBlockBounds (8.1s); completed successfully (3695 jobs).

`nice -n 5 lake env lean /home/scott/wt-scratch/nt-circle/BlockAxioms.lean`
checks both generic Fourier inequalities, the actual frequency and sawtooth
arc bounds, both geometric widths, and both local block bounds. The log is
`/home/scott/wt-scratch/nt-circle/block-axioms.log`.
Exit 0; all eight results use exactly `[propext, Classical.choice, Quot.sound]`.
Module checks pass for all 21 packet Lean files at the 1500-line cap; staged
whitespace checks pass.

The next missing steps are the exact disjoint integer-block covering (including
the endpoint discarded to meet the derivative test's extra endpoint) and the
height-sum/area comparison. The global uniform circle bound remains unproved;
goals 3–5 have not been claimed complete.

## Final goal-2 progress: global sawtooth estimate, area comparison open

Integration: after the orchestrator's landing notice, committed the optimized
block milestone as `6e8de12`, then ran `git merge main`. Merge `2f0477f` includes
main `00d139a`, without conflicts. Read the updated COMMON, D6, and findings.
`LatticeDisc.lean` now imports the sealed frozen definition and characterizes
membership using **`WaveTurbulence.latticePoint 1 n`**. Its former local unit
embedding was removed; no frozen declaration was edited. All new changes are
inside the packet's owned directories.

The following additional steps are proved:

- `Counting/MonotoneIntervals.lean`: an exact half-open height filter of a
  monotone natural sequence on `(a,b]` is another natural interval.
- `Counting/DyadicBlocks.lean`: existence and uniqueness of the dyadic height
  index, the exact finite-sum partition into low heights and disjoint blocks,
  `sum_{j<J} R/2^(j+1) <= R`, and a terminal cutoff in `[r^2,2r^2)` for radius `r^3`.
- `Counting/CircleBlockIntervals.lean`: the actual filtered integer block has
  sawtooth sum at most `323H/r`. Its last point is included separately, so the
  derivative test's extra real endpoint is fully accounted for.
- `Counting/CircleLowHeights.lean`: low-height columns have cardinality at most
  `L^2/R+1`; at cutoff `L<=2r^2`, their sawtooth contribution is at most `3r^2`.
- `Counting/CircleSemicircle.lean`: actual left and right semicircle sums are
  bounded by `326r^2`, and their combined bound is `652r^2`.

The complete strongest global statement is `circle_sawtooth_sum_le`:

    forall {r c t d : R} {a b : N},
      1 <= r -> c-r^3 <= a+1+t -> b+t <= c+r^3 ->
      |sum_{k in Ioc a b} sawtooth(circleHeight (r^3) c (k+t) + d)| <= 652*r^2.

There is no premise asserting any exponential sum, sawtooth estimate, count,
or discrepancy bound. The four real parameters are arbitrary apart from
the radius and geometric interval conditions. Reflection uses an exact
permutation of the integer indices. Constants do not depend on either shift.

Final focused successful checks (default budgets, sequential wt-throttled):

    nice -n 5 lake build WaveTurbulence.Foundations.Counting.LatticeDisc
    # Built Frozen.Defs.Mom (5.8s), Frozen.Defs.LatticePoint (3.0s),
    # ...LatticeDisc (6.5s); completed successfully (9055 cached/project jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.Counting.MonotoneIntervals
    # Built ...MonotoneIntervals (7.5s); completed successfully (3137 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.Counting.DyadicBlocks
    # Built ...DyadicBlocks (14s); completed successfully (3137 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.Counting.CircleBlockIntervals
    # Built ...CircleBlockIntervals (29s); completed successfully (3697 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.Counting.CircleLowHeights
    # Built ...CircleLowHeights (21s); completed successfully (3262 jobs).
    nice -n 5 lake build WaveTurbulence.Foundations.Counting.CircleSemicircle
    # Built ...CircleSemicircle (8.3s); completed successfully (3700 jobs).

All final builds above have zero warnings. The newly compiled frozen modules
are sealed definitions, not draft theorems/providers. No Mathlib module was
compiled, no root build was run, and no dependency artifacts were deleted.

    nice -n 5 lake env lean /home/scott/wt-scratch/nt-circle/GlobalArcAxioms.lean
    # exit 0; /home/scott/wt-scratch/nt-circle/global-arc-axioms.log

Eight axiom checks cover filtered blocks, low heights, exact dyadic partition,
cutoff existence, left/right/global arc sums, and the canonical disc membership
characterization. Every check reports exactly
`[propext, Classical.choice, Quot.sound]`. The probe also prints the two main
statement types, confirming their geometric premises and canonical lattice use.

The module checker passes for all 26 packet Lean files at the 1500-line cap.
Whitespace checks are clean. A scan of the owned `.lean` files finds no
`sorry`, `axiom`, `admit`, `unsafe`, `opaque`, or option overrides.

### Exact remaining mathematical obligation and proposed route

The circle discrepancy theorem has **not** been proved. After approximately an
hour on goal 2, the remaining analytic estimate is the following uniform
height-sum/area comparison, stated here as an obligation, not as a hypothesis
of any claimed circle theorem:

    exists C, forall r>=1 and c in R,
      |2 * sum_{x in integerInterval (c-r^3) (c+r^3)} circleHeight (r^3) c x
           - pi*r^6| <= C*r^2.

The exact disc formula in `LatticeDisc.lean` already isolates this term and
two sawtooth sums. The latter are controlled by the proved global arc estimate
after reindexing the integer interval by naturals. That interval reindexing,
the area estimate, and the final `Q=r^3` reparameterization still need to be
installed in Lean; none is silently discharged by the local/global arc results.

Proposed continuation: use a trapezoidal estimate on the truncated smooth
arc, with the height cutoff of order `r^2`, and monotone endpoint estimates
for the two tips. Mathlib's
`MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean` has
`trapezoidal_error_le` and `trapezoidal_error_le_of_c2`; the local derivative
and dyadic geometry bounds needed to apply them are proved in this packet.
The circular area integral can be obtained by scaling/translating Mathlib's
`intervalIntegral.integral_sqrt_one_sub_sq` (check the exact export namespace
when implementing). This is a proposed proof route, not a completed Lean proof.

No new suspected source errata or counterexample to revision 2 was found.
The deviation is a partial handoff at its goal-2 stop condition: goal 1 is done
and committed; the substantial circle ingredients above are separate milestones.
Goals 2–5 are not claimed done, and no improved discrepancy exponent is reported
as proved. The old exponent audit remains a numerical audit, not goal 5.

The preceding STOPPED status is superseded by the continued work below.

## Continued work: goal 2 completed (2026-11-03)

The orchestrator clarified that routine long proofs are not stop conditions.
The Euler–Maclaurin route is implemented without additional mathematical assumptions.

Files: `Counting/EulerMaclaurin.lean`, `CircleAreaGeometry.lean`,
`CircleQuadrature.lean`, `IntegerSampling.lean`, `CircleHeightSum.lean`,
`CircleIntegerSawtooth.lean`, `CircleDiscrepancy.lean`.

Approach: twice integrate by parts on each unit interval against
`(x-a)*(x-a-1)/2`, whose absolute value is at most `1/8`. For a concave
function the remainder is bounded by the decrease of the first derivative,
which telescopes. Circular slopes after removing unit tip regions are at
most `sqrt R`. Tip heights and tip integrals cost `O(sqrt R)`. Scaling
Mathlib's exact unit semicircle integral gives `pi*R^2/2`. The actual closed
integer height sum differs from this area by at most `15*sqrt R` for all
`R >= 1` (the small-radius case is handled directly). Exact reindexing
transfers the global sawtooth estimate to the same integer columns.

Main result: `abs_card_latticeDisc_sub_area_le`, for every `Q >= 1` and
`c : EuclideanSpace ℝ (Fin 2)`,
`abs (card(latticeDisc c Q) - pi*Q^2) <= 1334*Q^(2/3)`.
`mem_latticeDisc` identifies this finite set exactly with the closed norm
condition using the canonical frozen `WaveTurbulence.latticePoint 1`.
No boundary points or exceptional centers are omitted.

Checks: targeted `nice -n 5 lake build
WaveTurbulence.Foundations.Counting.CircleDiscrepancy` completed successfully
(9074 jobs, final own-file build 8.6s), with no warnings and default budgets.
The intermediate quadrature build and its five axiom checks passed; their
axioms are only `[propext, Classical.choice, Quot.sound]`.

Commits: `3037cae` (integral remainder and slopes), `9e336c7` (full circular
quadrature); main merged at the clean milestone. Goal 2 is now proved;
goals 3–5 remain in progress. No new suspected errata or deviations.

The final discrepancy axiom probe `CircleDiscrepancyAxioms.lean` passed for
both discrepancy forms, the actual integer height and sawtooth sums, and
`mem_latticeDisc`: all have only `[propext, Classical.choice, Quot.sound]`.
The module-shape check passes for all 33 owned Lean modules.

## Goal 3: elementary geometry milestone (in progress)

Files: `Counting/LatticeTriangle.lean`, `QuadraticStrip.lean`, `AnnulusLine.lean`.
The thin-frame determinant criterion is proved by integrality of the doubled
lattice-triangle area. Degenerate planar lattice sets have an injective
coordinate projection, and nonvertical ones have the actual affine graph
through two distinct points. Quadratic-strip counting handles both branches
and proves `card_collinear_radial_annulus_le`: every collinear finite lattice
subset of the actual radial annulus has at most `8*sqrt(Q*rho)` points when
`0 <= rho <= Q` and `Q*rho >= 1`. Vertical lines, singletons and empty sets
are included. This is the line-counting step of DH23 L2042, not yet the full
elementary branch: its thin-section covering remains to be assembled.

Checks: targeted `nice -n 5 lake build
WaveTurbulence.Foundations.Counting.AnnulusLine` completed successfully
(3216 jobs; final own-file build 34s), no warnings or budget overrides.
No additional source defect or deviation was found. Goal 3 remains active;
goals 4–5 are not claimed complete.

The four main elementary-geometry axiom probes also passed, all with only
`[propext, Classical.choice, Quot.sound]`.
