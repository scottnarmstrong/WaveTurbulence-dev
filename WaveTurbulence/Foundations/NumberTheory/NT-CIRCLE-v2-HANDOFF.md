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

## Goal 3: elementary annulus branch completed

Additional files: `Counting/AnnulusSectionGeometry.lean`, `IntervalCells.lean`,
`AnnulusCellWidth.lean`, `AnnulusChartCounting.lean`, `LatticeRotations.lean`,
`AnnulusRotatedCharts.lean`, `AnnulusCoverGeometry.lean`, `AnnulusElementary.lean`.

Main result `card_annulus_disc_le` counts any finite subset of the actual
annulus–disc intersection, using `WaveTurbulence.latticePoint 1` and the
Euclidean carrier for both centers. The bound is
`640000*(1 + L*rho + L/Q^(1/3))*sqrt(Q*rho)`.
This is the factored form of DH23's three elementary terms:
`sqrt(Q*rho) + L*(Q*rho)^(3/2)/Q + L*sqrt(Q*rho)/Q^(1/3)`.
The explicit scale convention is `Q > 0`, `0 <= rho <= Q/2`, `Q*rho >= 1`,
and `L >= 0`; `rho` is the annulus half-width. These fix constants in the
source's `Q^(-1) << rho << Q` and its width convention. No exceptional
centers or integer boundary points are discarded.

Approach: use four Cartesian charts instead of angular sectors. On the
upper chart `y >= Q/4`, a horizontal cell of width `T` has tangent-shear
thickness at most `1000*(rho + T^2/Q)`. With radius `r^3`, the explicit
choice `T = 1/(10000*(1/r+rho))` makes the determinant bound less than one.
Every cell is therefore collinear. The previously proved line estimate and
the actual floor-cell count `2L/T+2` give the upper-chart bound; exact lattice
quarter-turn embeddings handle the other three charts. The four charts
cover the whole annulus. The intermediate square version is stronger than
the requested containing-disc version.

Checks: targeted `nice -n 5 lake build
WaveTurbulence.Foundations.Counting.AnnulusElementary` passed (9059 jobs,
final own-file build 6.7s), zero warnings, default budgets. Each supporting
module was also built narrowly. This completes only goal 3's elementary
annulus branch. The `estcross` part remains active, starting with a direct
floor-cell proof of the short-relation pigeonhole step in `DenseStrip.lean`.
No new suspected source errata. The Cartesian subdivision is a proof-route
choice, and the half-width and small-width constants above are explicit
conventions rather than changes to the asymptotic claim.

All six annulus-elementary axiom probes passed, each with only
`[propext, Classical.choice, Quot.sound]`. The module-shape check passes
for all 45 owned Lean files currently present.

## Goal 3: estcross density and separable-counting milestone

Files: `Counting/DenseStrip.lean`, `DenseProductStrip.lean`, `LatticeBox.lean`,
`FiniteFibers.lean`, `LinearStrip.lean`, `SeparableStrips.lean`.

The planar short-relation pigeonhole step is proved with explicit constants:
if a strip has at least `L/theta` samples, `L >= 16*theta`, the first coefficient
has absolute value greater than `2*rho` and dominates the second, then there
is an actual nonzero second integer coefficient of magnitude at most `8*theta`,
a first coefficient of magnitude at most `9*theta`, and linear error at most
`2*rho`. The higher-dimensional product version proves the coordinate-fixing
step via actual finite fibers, with theta enlarged by `3^d` for `d` remaining
coordinates. No planar density is assumed without proving it from the full
family's density.

Integer boxes have proved cardinal bound `(2L+1)^d`, uniformly in real centers.
One-dimensional linear strips have bound `2*rho/abs a + 1` and, when the
coefficient is dominated by the width, `3*rho/abs a`. The independent pair
of linear constraints is counted after fixing the other coordinates in
`card_separable_strips_le`. These are generic geometric/counting helpers;
they do not stand in for the source `estcross` theorem. Summing over short
relations and discharging their witnesses for the full exceptional set remain.

Checks: targeted `DenseProductStrip` build passed (9061 jobs, final own file
8.6s); targeted `SeparableStrips` build passed (9060 jobs, final own file 3.3s).
All supporting files compile without warnings, default budgets. No new source
erratum or deviation has been found.

The five estcross-ingredient axiom probes passed, all with only
`[propext, Classical.choice, Quot.sound]`.

## Goal 3 completed: full estcross and source-form annulus bound

Additional files: `Counting/RelationIndices.lean`, `ShortRelationCounting.lean`,
`LatticeCoordinates.lean`, `DenseVectorStrip.lean`, `DenseRelationIndices.lean`,
`EstcrossBudget.lean`, `EstcrossDominant.lean`, `Estcross.lean`, `EstcrossBalls.lean`.
The expanded elementary annulus form was added to `AnnulusElementary.lean`.

Main result `card_dense_dot_product_strips_in_balls_le` states estcross for
actual Euclidean balls and the actual inner product of frozen
`WaveTurbulence.latticePoint 1` values. It covers every dimension `D=d+3`.
The source's global standing dimension assumption is explicit at DH23 TeX
L252 and L438: `d >= 3`. The ball centers and levels of the dense strips may
depend arbitrarily on the exceptional vector; no center is bounded or rounded.
The density condition is an actual finite subset of the ball with actual
strip membership and at least `L^(D-1)/theta` points. It is exactly the
property being counted, not an intermediate short-relation hypothesis.

The proved bound is
`C_D * (rho^D + L^(D-2)*rho^2*theta^2*(1+log L)^2)` with
`C_D = 5^D + D*129600*(3^(D-2))^3`.
Explicit scale convention: `rho >= 0`, `theta >= 1`,
`16*3^(D-2)*theta <= rho <= L`. This fixes constants in the source's
`1 << rho << L`, `1 <= theta << rho`. The dense-count threshold is normalized
to `L^(D-1)/theta`; other fixed implicit constants can be absorbed into theta
and the corresponding scale constants. The theorem does not require dyadic
parameters and its explicit logarithmic loss is only two powers.

Approach: the actual coordinate dot product and its remaining-coordinate
fibers provide each of the two short integer relations. Signed nonzero
coefficients are enumerated by their actual sign and positive natural
magnitude. Counting the two remaining independent coordinates gives reciprocal
weights; their exact sum is a harmonic number, bounded by Mathlib's
`harmonic_le_one_add_log`. The actual coefficient budget is the natural ceiling
of `9*3^(D-2)*theta`, bounded by `10*3^(D-2)*theta`. The dominant-coordinate
restriction is removed by actual coordinate permutations and a finite cover.
Small vectors contribute the `rho^D` term. No short-relation witnesses or
coefficient-sum estimates are left as premises of estcross.

`card_annulus_disc_le_expanded` now states the elementary annulus branch with
exactly the three printed geometric terms, using a proved identity between
the factored expression and real powers. It retains the closed radial annulus
and closed Euclidean containing disc, uniformly in both centers.

Checks: targeted `nice -n 5 lake build
WaveTurbulence.Foundations.Counting.EstcrossBalls` passed (9072 jobs, final
own-file build 16s) and targeted `AnnulusElementary` passed (9059 jobs, final
own-file build 26s), both with no warnings or budget overrides. The module
shape/line-limit check passes for all 59 owned Lean modules. `git diff --check`
is clean. All short-relation, scalar-budget and coordinate modules compiled
through these exact targets. Goals 1–3 are proved; goal 4 is next, and goal 5
still depends on its improved exponent.

New minor source erratum: DH23 `Revision_Submit.tex` L2040 prints
`\#(A\cap \Zb^d)` in the elementary planar-annulus proof. The lemma begins with
`A\subset\Rb^2` (L2028), so that display should read `Z^2`. The formalization
uses `Fin 2 -> Z` throughout this argument. This is a dimensional typo and
does not affect the estimate. The previously accepted F31 numerical defect
and the requirement for an exponent strictly below `2/3` remain unchanged.

Final goal-3 checks: the six estcross axiom probes, including the full
Euclidean-ball theorem, passed, all with only `[propext, Classical.choice,
Quot.sound]`. The expanded annulus theorem and its real-power identity also
passed the same axiom check. No provider, draft frozen theorem, custom axiom
or budget override is used. Goal 3 is complete and work proceeds directly
to goal 4.

## Revised goal 4 coordination and general smoothing milestone

The orchestrator split the B-process into NT-BPROC (wt-ansob), owning
`Foundations/VdCB/**`, including the Graham–Kolesnik phase-class predicate
and `IsExponentPair`. This packet defines no competing exponent-pair notion.
It now supplies the A-process side, distinct conditional transfer helpers,
and the general-exponent annulus bound, then will plug in VdCB's proved pair
and finish goal 5. Coordination is only through the orchestrator.

New proved files: `NumberTheory/PhaseCalculus.lean`, `FractionalPowerSums.lean`,
`FractionalSmoothing.lean`, `ExponentPairSmoothing.lean`.
For `0 < kappa < 1`, the exact weight bounds are
`sum_{n<=H} n^(kappa-1) <= H^kappa/kappa` and
`sum_{n>H} n^(kappa-2) <= H^(kappa-1)/(1-kappa)`.
Consequently the sawtooth sum is bounded by
`card/(2H) + ((pi/kappa+1/(1-kappa))/pi^2)*A*H^kappa`
under the explicit actual frequency estimate `norm(S_n) <= A*n^kappa`.
`abs_sum_sawtooth_le_of_frequency_scale` optimizes the actual natural cutoff
`ceil(Q^((1-lambda)/(1+kappa)))`, for `lambda <= 1`, and proves the exact
exponent `(kappa+lambda)/(1+kappa)`, with no logarithmic or epsilon loss.
It assumes an actual finite phase family's frequency estimate and is named
and documented as a conditional numerical helper. No improved exponent pair
or improved unconditional circle estimate is claimed at this stage.

Checks: targeted `ExponentPairSmoothing` build passed (3718 jobs; supporting
own-file builds 70s and 64s) and `PhaseCalculus` passed (3256 jobs, 61s), no
warnings or overrides. All five corresponding axiom probes passed with only
`[propext, Classical.choice, Quot.sound]`.
The unfinished Poisson and oscillatory-integral drafts were preserved under
`/home/scott/wt-scratch/nt-circle/bproc-drafts/`, outside the repository, after
the B-process was reassigned. The completed phase-calculus identities remain
available as reusable character calculus; no B-process source theorem is
being implemented in this packet in parallel with NT-BPROC.

## Conditional circle and annulus transfer

`Counting/CircleExponentTransfer.lean`, `AnnulusDiscrepancy.lean`, and
`CircleExponentAnnulus.lean` compile. The explicit actual column-frequency
hypothesis implies discrepancy at exponent `(kappa+lambda)/(1+kappa)` with
constant `33+4*((pi/kappa+1/(1-kappa))/pi^2)*C`, for `0<kappa<1` and
`1/2<=lambda<=1`. No exponent-pair predicate is defined and no improved
unconditional discrepancy is claimed. The annulus comparison, independently
of this hypothesis, gives `6*pi*Q*rho+3*C*Q^e` from a circle error `C*R^e`,
for `Q>=2`, `0<rho<=Q/4`, `0<=e<=1`. The inner disc has radius `Q-2*rho`, so
closed radial boundaries introduce no subtraction error. Specialization to
the proved two-thirds theorem gives `6*pi*Q*rho+4002*Q^(2/3)` unconditionally.
The minimum with the full elementary branch is also proved.

Check: `nice -n 5 lake build
WaveTurbulence.Foundations.Counting.CircleExponentAnnulus` passed (9092 jobs;
final own-file builds 89s and 81s), no warnings or budget overrides.

The orchestrator's new proposed chain `BAABAAB` from `(0,1)` has coordinates
`(1/2,1/2)`, `(1/6,2/3)`, `(1/14,11/14)`, `(2/7,4/7)`,
`(1/9,13/18)`, `(1/20,33/40)`, `(13/40,11/20)`.
Its circle exponent is exactly `35/53`, with gap `1/159` below `2/3`.
The numerical DH23 critical-gamma branch optimization gives `63/79`, a gain
`1/395` below `4/5`, splitting at `q=477/395`. These numerical comparisons
are separate from the still-required proof and application of the pair.

## Quantitative A-process side

`NumberTheory/AProcessBounds.lean` reduces the actual integer-window Weyl
inequality to `2*N^2/H+4*N*A*H^kappa`, chooses the integer cutoff `floor X`,
and proves norm at most `3*N/sqrt X` under the explicit balancing condition.
`AProcessOptimization.lean` proves the scalar A-coordinate transformation
`(kappa/(2*kappa+2),(kappa+lambda+1)/(2*kappa+2))`, with coefficient
`Y^kappa*N^(lambda-kappa)`, in the explicitly stated balanced-cutoff regime.
These are numerical helpers for actual finite differenced sums, with all
cutoff restrictions visible. They do not claim the full shared phase-class
A-closure theorem or define a second exponent-pair notion.
Check: `nice -n 5 lake build
WaveTurbulence.Foundations.NumberTheory.AProcessOptimization` passed (3263
jobs, own-file builds 45s and 25s), no warnings or budget overrides.

## Octant integration in progress

To apply the newly coordinated square-root power-profile class uniformly in
the real center, the improved circle route now uses the central inscribed
square plus four outer caps. The caps have strict artificial cuts; their
circular boundaries stay closed. Clipping each semicircle at `T=R/sqrt 2`
absorbs the square's terms linear in R. The remaining square correction is
a product of two sums of sawtooth values, hence bounded by one. The central
excess removed by clipping has slope at most one and quadrature error at
most four, so clipping preserves the proved square-root quadrature error.

Compiled ingredients: `Counting/CircleCentralArc.lean` (bounded slope,
Lipschitz estimate, central trapezoidal error <=1/4),
`CircleCentralQuadrature.lean` (central excess sample error <=4), and
`LatticeCoordinateSwap.lean` (actual frozen embedding, Euclidean center,
exact interchange of horizontal and vertical cap counts). Targeted
`CircleOctantCounting` builds compiled these supporting modules in 73s,
55s, and 57s respectively, no warnings. The target's subsequent errors
were local endpoint and finite-sum elaboration issues in other modules;
the full octant transfer is not yet claimed.

The four circle/annulus transfer axiom probes passed with only
`[propext, Classical.choice, Quot.sound]`.

The next compiled octant ingredients are `CircleOctantGeometry.lean`
(exact finite square/cap partition, central square product count, residual
square correction <=1) and `CircleClippedHeight.lean` (exact subtraction of
the central integer excess and clipped quadrature error <=15*sqrt(R)+4).
The targeted `CircleOctantCounting` build compiled them in 68s each, without
warnings. Subsequent cap-slice and assembly modules are being checked.

`CircleCapCounting.lean` and `CircleOctantCounting.lean` now compile too:
the exact closed-disc cardinality is the central integer-rectangle product
plus the two vertical and two horizontal cap sums. Each slice is exactly
`2*height-psi(height+c_other)-psi(height-c_other)`. Both cap height sums are
proved equal to their clipped height sums minus the flat central count.
Check: `nice -n 5 lake build
WaveTurbulence.Foundations.Counting.CircleOctantCounting` passed (9067 jobs;
final own-file build 60s), no warnings.

## Outer-octant transfer compiled

`CircleOctantArea.lean` proves the central arc area
`R^2*(pi/4+1/2)` and central excess area `R^2*(pi/4-1/2)` by actual sine
substitution. `CircleOctantError.lean` unconditionally bounds the translated
closed-disc discrepancy by four actual outer-cap sawtooth sums plus
`60*sqrt(R)+17`. `CircleCapSmoothing.lean` handles the actual cap filters
and arbitrary vertical phase shifts. `CircleOctantTransfer.lean` proves the
conditional general-exponent transfer using only the outer-cap frequency
hypothesis, uniformly in both center coordinates:

`forall j : Fin 2, forall n>0,
 norm(sum_{x in integerInterval(c_j-R,c_j+R), R/sqrt(2)<abs(x-c_j)}
      expPhase(n*circleHeight R c_j x)) <= C*R^lambda*n^kappa`.

For `0<kappa<1`, `1/2<=lambda<=1`, the resulting circle exponent is exactly
`(kappa+lambda)/(1+kappa)`. The constant is
`83+8*((pi/kappa+1/(1-kappa))/pi^2)*C` for `R>=2`, or the harmless uniform
`2668+8*((pi/kappa+1/(1-kappa))/pi^2)*C` for every `R>=1`. This is a distinct
conditional helper, not a claim that the exponent pair is already proved.
It replaces the earlier all-column input with the exact outer-octant input
needed by the coordinated square-root power-profile class.

Check: `nice -n 5 lake build
WaveTurbulence.Foundations.Counting.CircleOctantTransfer` passed (9090 jobs;
final own-file build 15s), with zero warnings after cleanup. No budgets or
extra assumptions about integer endpoints or the center are used.

`CircleOctantAnnulus.lean` also compiles: the uniform outer-cap frequency
hypothesis supplies both the general-exponent annulus branch and its minimum
with the proved elementary geometric branch. The actual closed annulus and
containing disc are unchanged. Targeted `CircleOctantAnnulus` build passed
(9103 jobs; own-file build 5.2s), zero warnings.

`NumberTheory/AProcessAllRegimes.lean` removes the artificial cutoff regime
from the numerical A-process helper when `Y>=1`, `0<=kappa<=lambda` and
`N>0`. The optimal cutoff is automatically <=N; if it is <1, the actual
trivial finite exponential-sum bound suffices. It proves the A-transformed
coordinates from actual differenced sums, with no phase-class predicate
introduced. Targeted `AProcessAllRegimes` build passed (3264 jobs, own-file
4.0s), zero warnings.

The merged independent infrastructure audit's L1 notes a registry omission:
`Counting/MonotoneIntervals.lean` is salt-adapted with its required per-file
attribution and license pointer, but the orchestrator-owned
`docs/THIRD-PARTY.md` list omits it. That registry still needs its file list
extended. No out-of-ownership documentation edit was made here.

## Proposed 35/53 exponent: numerical audit checked

`Counting/ImprovedExponentAudit.lean` proves the scalar `BAABAAB` chain
coordinates `(13/40,11/20)`, the resulting exponent `35/53`, and its strict
`1/159` improvement over `2/3`. These scalar identities do not assert that
the analytic exponent-pair closure has landed.

For DH23 `basiccount0` (1), L2077, and (3), L2088, the complete two-branch
expression with exponent `35/53` is <=
`1-min(1/1000,2*gamma-1)` for every `gamma>=1/2` and every q. Thus it retains
the exact fixed saving stated in the source even near `gamma=1/2`.
For (2), L2082, the correctly summed branches are <=`63/79=4/5-1/395`, split
at `q=477/395`. An explicit eta-margin lemma proves
`63/79+D*eta <= gamma-20*eta` whenever
`gamma>=4/5-10*eta` and `(D+30)*eta<=1/395`. This allows the source's fixed
`O(eta)` losses for sufficiently small eta. For `basiccount` (5), L2117,
the previously proved geometric-branch comparison is unchanged and does
not depend on the circle exponent. The former two-thirds comparisons for
(1),(3) also follow monotonically whenever q>=0.

Check: targeted `ImprovedExponentAudit` build passed (3138 jobs, 2.9s), zero
warnings. Goal 5's numerical work is ready for specialization, but its final
claim still requires an actually proved exponent pair and its application.

## Endpoint dyadic bridge compiled

`Counting/DyadicPowerBlocks.lean` extends the exact dyadic partition to any
additive commutative monoid, including complex sums, and proves the finite
geometric tail bound. `CircleEndpointBlocks.lean` proves the unit-scale
cutoff and an absolute bound of six terminal columns. It derives the global
sum bound from actual local complex block estimates.
`CircleEndpointFrequency.lean` normalizes the endpoint power scale
`n^kappa*R^(kappa/2)*U^(lambda-kappa/2)` and proves the global outer-cap
frequency estimate with constant
`6+C/(2^(lambda-kappa/2)-1)` multiplying `R^lambda*n^kappa`, for
`0<=kappa<1`, `lambda>=1/2`, natural n>0, and R>=1. No logarithm, epsilon,
phase-class definition or hidden endpoint estimate is introduced.
The local block premise is explicit and named as a conditional helper.

Check: `nice -n 5 lake build
WaveTurbulence.Foundations.Counting.CircleEndpointFrequency` passed (9060
jobs, final own-file build 5.7s), zero warnings.

Read-only inspection of VdCB's current API confirms that analytic A/B
closure is still in progress. Its generic decreasing-power class is not
claimed to contain every circle block with arbitrarily small perturbation;
its documented direct-circle route uses the actual Legendre dual and a
uniform fifth-derivative estimate. Our outer-cap and block consumers make
no unsupported inference from the generic predicate. They can consume the
proved direct-family bound as soon as it lands, preserving arbitrary centers.

`CircleOctantPhase.lean` compiles: both actual endpoint formulas,
`circleHeight R c (c+R-u) = sqrt(2R)*sqrt(u)*sqrt(1-u/(2R))`
and its left reflection, hold for R>0,u>=0. The factor has all finite
smoothness orders on t<2 and lies in [1/2,1] on [0,1]. These identities do
not assert arbitrary-small perturbation membership in the generic profile
class. Targeted `CircleOctantPhase` passed (3260 jobs, 2.2s), zero warnings.

Seven new main axiom probes passed: all-regime A optimization, central
quadrature, exact cap count, central area, outer-sawtooth reduction,
outer-frequency circle transfer, and complete annulus minimum. Each has
only `[propext, Classical.choice, Quot.sound]`. Exact check:
`nice -n 5 lake env lean /home/scott/wt-scratch/nt-circle/OctantAxioms.lean`
exited 0.

`NumberTheory/PhaseDifferences.lean` compiles: actual finite differences
commute with first and higher derivatives at the two evaluation points,
and the real mean-value theorem transfers absolute derivative bounds with
the exact shift factor. No sign hypothesis or exponent-pair definition is
introduced. Targeted `PhaseDifferences` build passed (3231 jobs, 3.6s), zero
warnings. Further A-iterations are being prepared using the already mined
salt third-difference proof and our existing character/Weyl toolkit.

## Analytic A-iteration: third differences and both power terms

`NumberTheory/ThirdDifference.lean` adapts the already pinned, licensed salt
`Salt/ExpSum/DerivTest.lean` proof to the existing `expPhase`, second-difference
and exact Weyl modules. It proves the third finite-difference test
`12*sqrt(c)*(N*lambda^(1/6)+N^(1/2)*lambda^(-1/6))`, including every lambda
regime and actual integer overlap. It also exports the integer-indexed
second-difference wrapper, exact symmetric integer shift summation, and
negative-shift conjugation symmetry. The only change in the Weyl invocation
uses our stronger all-N,H theorem instead of salt's extra cutoff arguments.
Headers and source commit attribution are retained; no budgets were changed.
The orchestrator-owned third-party registry should additionally list this
salt-derived `NumberTheory/ThirdDifference.lean` file (same existing license).

`AProcessTwoPowers.lean` proves the general actual-shift bound
`|S|^2 <= 2*N^2/H+4*N*A*H^alpha+
 (4*N*B/(1-alpha))*H^(-alpha)` for `0<alpha<1`, `1<=H<=N`, from the two
actual shift terms `A*h^alpha+B*h^(-alpha)`. The negative powers use the
proved fractional integral estimate, and both shift signs are included by
exact conjugation. This supports further A-iterations without discarding
the negative-power error term.

Check: targeted `AProcessTwoPowers` build passed (3556 jobs; own-file builds
13s and 2.4s), zero warnings. These are actual derivative/difference tests
and distinct numerical A-process helpers; no shared phase class is redefined.

`FiniteDifferenceMeanValue.lean` proves, for every natural n, that the actual
n-fold unit finite difference equals the n-th member of an actual derivative
tower at some point in the full sample interval `[x,x+n]`. It also proves
commutation with derivatives and the explicit second/third formulas.
`ThirdDerivative.lean` applies this to the proved third-difference test,
including the negative-third-derivative case via exact phase conjugation.
Its source interval includes the two extra right-hand sample units, so no
off-interval derivative values are assumed silently. Targeted
`FiniteDifferenceMeanValue` passed (3232 jobs, 2.2s), and `ThirdDerivative`
passed (3268 jobs, 1.8s), zero warnings.
