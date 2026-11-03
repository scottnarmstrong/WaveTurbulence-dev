# NT-CIRCLE-v2 progress and handoff

Goal 1 complete. Goals 2–5 remain open; no circle discrepancy, annulus count,
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
