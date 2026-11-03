# NT-BPROC progress

Branch `w/bproc`, based on `main` in the former AN-SOB worktree. Owned namespace and files:
`WaveTurbulence.VdCB`, `WaveTurbulence/Foundations/VdCB/**`.

Checked foundation: `Phase`, `IntegrationByParts`. The phase is the existing
`NumberTheory.expPhase`; the chain rule, `2π` Lipschitz estimate, interval-length bound and
exact oscillatory integration-by-parts formula are proved. Check:
`nice -n 5 lake build WaveTurbulence.Foundations.VdCB.IntegrationByParts` returned
`Build completed successfully (3510 jobs).`, no warnings.

No truncated-Poisson, stationary-phase or B-process theorem is yet claimed.

API issue raised with the orchestrator: a bare absolute derivative-comparability phase
class is not stable under the B-transform. The resonant `x^(3/2)` example in Olivier
Robert, *On van der Corput's k-th derivative test for exponential sums*, Lemma 7,
https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf, has a main term of order
`N^(3/4)`. For `F=N^(3/2)`, the requested pair `(11/30,16/30)` would give `N^(43/60)`.
Robert Section 5 explains the need for stable semi-monomial classes; the conventional
model profile has decreasing first derivative `x^(-s)`, `s>0`, with controlled perturbations.
A clarification was requested; generic analytic work continues independently.

Further checks: `NonstationaryIdentity` passed (`Build completed successfully (3511 jobs).`)
and `EulerCell` passed (`Build completed successfully (2789 jobs).`), without warnings.
The nonstationary formula uses actual `deriv f` and `deriv (deriv f)` under C² smoothness
and nonvanishing on the interval. Euler cell summation has the exact midpoint endpoint
terms and handles the right-continuous sawtooth by null endpoint changes.
The three packet goals are still in progress; these are proved ingredients only.

Checked `QuadraticTaylor` and `LocalStationary`: actual third-derivative bounds yield
`|f(x)-Q₂(x)|≤M |x-c|³/6` and the radius-`r` oscillatory comparison error
`(2π/3) M r⁴`, including factorization at a critical point. Targeted
`nice -n 5 lake build WaveTurbulence.Foundations.VdCB.LocalStationary` returned
`Build completed successfully (3528 jobs).`, no warnings. The Fresnel constant and
complementary nonstationary tails remain to be assembled; no full stationary-phase
or B-process theorem is claimed yet.

Orchestrator approved the decreasing-power profile on 2026-11-03 and additionally required
coverage of the circle phase `h sqrt(2Ru-u²)` on dyadic octant blocks. Shared API draft is
in `ModelPhase`, `ExponentPair`, with the broad derivative-comparability predicate retained
separately in `DerivativeClass`. The quantifiers choose `(R,δ,C)` for each fixed `s>0`
before `(N,F,f,a,b)`. The trivial pair uses the unconditional `2N` lattice-count estimate.
No B-closure is encoded into either the phase-class or exponent-pair definitions.

For the circle coverage, the direct-family option is being used. Its exact dual is
`R(sqrt(h²+ν²)-ν)`; at order five its derivative is
`15 R h² ν (3h²-4ν²) (h²+ν²)^(-9/2)`, nonzero for `ν≥h>0`.
`CircleDualCalculus` contains these explicit formulas and their calculus proofs (not yet
checked). This allows the repeated A-process/fifth-derivative estimate on the dual curve
without claiming that arbitrary bounded multiplicative perturbations are B-stable.

Uncommitted files are under targeted validation; source estimates are not yet complete.

The shared interface and current tools now pass targeted `VdCB.Basic` (3808 jobs), without
warnings. The scratch `BasicAxioms.lean` consumer exited 0; trivial pair, Euler summation,
smooth Poisson, nonstationary bound and harmonic block bound all have only the standard
three axioms. See `API.md` for the exact exported contracts and remaining closure work.

Checked direct circle-family modules: `CircleDualCalculus`, `CircleDualBounds`,
`CircleLegendre`, `CircleLatticeDual`. The actual stationary point solves the derivative
equation, and its Legendre value is proved. The `u=R-n` shifted lattice is retained:
the original integer-column dual is `R sqrt(h²+ν²)`, not `R(sqrt(h²+ν²)-ν)` when `R`
is nonintegral. The linear correction changes no fifth derivative. On `[Y,2Y]`, `Y≥h>0`,
its magnitude lies between `Rh²/(125Y⁶)` and `480Rh²/Y⁶`, with no small-perturbation
hypothesis. These modules passed as dependencies of targeted `StationaryTools` checks;
that aggregate target is still being repaired in its separate Gaussian-boundary dependency.
Also checked: `MonotoneAmplitude` (uniform tail integration-by-parts estimate) and
`GaussianPairing` (exact regularized Fourier identity for a Schwartz amplitude).
No complete B-process or full finite-interval stationary-phase result is yet claimed.

The exact Schwartz-amplitude quadratic Fourier identity now builds, including
its principal-branch coefficient `expPhase (1/8) / sqrt q`. The Gaussian
pairing identity extends to imaginary parameters by dominated convergence.
`CircleLatticeRegularity` exports global smoothness and actual within-interval
fifth-derivative bounds for the corrected integer-column dual. Checked target:
`nice -n 5 lake build WaveTurbulence.Foundations.VdCB.StationaryTools`:
`Build completed successfully (3813 jobs).` No warnings.

Checked sharp midpoint Poisson limit on natural endpoints:
`nice -n 5 lake build WaveTurbulence.Foundations.VdCB.PoissonSymmetricLimit`
returned `Build completed successfully (3541 jobs).` The proof uses the
finite Dirichlet kernel primitive, Euler summation, and dominated convergence
away from the null integer lattice. This is a limit, not yet the quantitative
truncation theorem. The paired distant reciprocal block is bounded by
`12*pi + 4*r/K` in `ReciprocalTail` (target passed, 3538 jobs).

`QuadraticStationary` proves the quadratic stationary-phase main term
`expPhase(1/8)*a(0)/sqrt(q)` with error bounded by
`pi/(q*sqrt(q))` times the second Fourier moment of the Schwartz amplitude
(target passed, 3786 jobs). This does not yet replace the general C3 stationary
expansion requested by the packet.

The scratch `StationaryAxioms.lean` probe (`nice -n 5 lake env lean ...`, exit 0)
printed only `[propext, Classical.choice, Quot.sound]` for the Fresnel coefficient,
exact quadratic Fourier identity, circle within-interval fifth-derivative bounds,
quadratic stationary estimate, sharp Poisson limit, and reciprocal block bound.

The normalized finite outer-frequency tail now builds:
`nice -n 5 lake build WaveTurbulence.Foundations.VdCB.NormalizedTail`
returned `Build completed successfully (3570 jobs).` For integer `a≤b`, actual
`0≤f'≤N` and `f''≥0`, it bounds the integrals over the two equally cut off
outer ranges by `(2*(1+log N)+4*log(N+1))/(2*pi)`, uniformly in the cutoff.
The proof preserves cancellation at integer endpoints and integrates the
square kernel using its logarithmic primitive. Modules `FrequencyIntegration`,
`FiniteFrequencyTail`, `OuterFrequencies`, `HarmonicTail`, `SquareKernel`, and
`LogKernel` contain its actual calculus and finite-sum ingredients.
The cutoff-to-limit assembly is being implemented; the full unnormalized
truncation statement and B-process are not claimed yet.
`QuadraticTail` also builds (3513 jobs), with the sharp positive quadratic
tail bound `1/(pi*q*a)` for `q,a>0`.

The normalized sharp truncated Poisson theorem now builds in `TruncatedPoisson`
(target 3822 jobs). On natural endpoints, `0≤f'≤N`, `f''≥0`, its half-open sum
minus the integrals over `ν∈Icc 0 N` has norm at most
`(2*(1+log N)+4*log(N+1))/(2*pi)+1`. The midpoint version omits the final one.
`FrequencyLimit`, `FrequencyPartition`, and `PoissonShiftedLimit` provide the
fully proved cutoff change; no summability of the absolute frequency series
is used. The four-export `TruncationAxioms.lean` scratch probe exited 0 with
only `[propext, Classical.choice, Quot.sound]`.

`WeightedStationary` builds (3805 jobs): for a Schwartz amplitude, an actual
stationary point at zero, positive actual second derivative q, and a bound M
on the actual third derivative along its support segments, the error is
`(pi*M/3)` times the cubic amplitude moment plus `pi/(q*sqrt q)` times the
second Fourier moment. The main term is `e(f(0)+1/8)*a(0)/sqrt q`.
General sharp-endpoint stationary phase and analytic B-closure remain open work.
