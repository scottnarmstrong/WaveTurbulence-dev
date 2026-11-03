# Shared NT-BPROC API (analytic closure still in progress)

Namespace: `WaveTurbulence.VdCB`. Consumers may import
`WaveTurbulence.Foundations.VdCB.ExponentPair` for the definitions and trivial pair;
`WaveTurbulence.Foundations.VdCB.Basic` additionally imports the current analytic tools.

- `integerInterval a b : Finset ℤ` is exactly `{n | a<n ∧ n≤b}`.
- `exponentialSum f a b : ℂ` is the actual sum of `NumberTheory.expPhase (f n)` on that set.
- `HasDerivativeBounds f N F R c C` is C^R smoothness on `[N,2N]` and the literal bounds
  `c F/N^r≤|f^(r)|≤C F/N^r`, `1≤r≤R`, with derivatives within the source interval.
  This alone is **not** the B-stable model class.
- `HasPowerProfile f N F s R δ` is C^(R+1) smoothness on `[N,2N]` and, for `0≤r≤R`,
  
  `|f^(r+1)(x) - (F/N^(r+1)) c(s,r) (x/N)^(-s-r)| ≤ δ F/N^(r+1)`.
  
  Here `c(s,0)=1` and `c(s,r+1)=c(s,r)*(-s-r)`; these are the derivatives of `u^(-s)`.
  This is the decreasing-power profile approved by the orchestrator.
- `IsExponentPair κ lam` includes the usual coordinate triangle, and has quantifiers
  
  `∀ s>0, ∃ R≥1, ∃ δ>0, ∃ C>0, ∀ N F f a b, ...`.
  
  The remaining hypotheses are `F≥N≥1`, `HasPowerProfile f N F s R δ`, and
  `N≤a≤b≤2N`. The conclusion is
  
  `‖exponentialSum f a b‖ ≤ C * (F/N)^κ * N^lam`.
  
  Thus all estimate constants and derivative order precede scales, phase, perturbation
  and interval. No closure results are fields/constructors of the predicate.
- `isExponentPair_zero_one : IsExponentPair 0 1` is proved using the unconditional `2N` bound.
- `bTransform (κ,lam) = (lam-1/2,κ+1/2)` and
  `aTransform (κ,lam) = (κ/(2κ+2),(κ+lam+1)/(2κ+2))` are coordinate maps only.
  Involution, B-triangle preservation and the word `B A³(1/2,1/2)=(11/30,16/30)`
  are proved. **Neither analytic A-closure nor analytic B-closure is claimed yet.**

Checked analytic tools:

- `euler_summation`: exact first-order sharp Euler formula on natural-number endpoints,
  including the half-endpoint correction and proved integrability of its sawtooth term.
- `poisson_amplitude_expPhase`: actual smooth compact-amplitude Poisson identity.
- `integral_expPhase_nonstationary`: exact identity dividing by the actual phase derivative.
- `norm_integral_expPhase_le_of_deriv_pos`: `1/(π lam)` for positive increasing derivative
  bounded below by `lam`, with C² smoothness and explicit actual derivative hypotheses.
- `norm_sawtoothFourier_sub_le_six`: uniform symmetric harmonic cancellation.
- `norm_integral_sub_stationary_quadratic_le` (import `LocalStationary`): the actual
  third-derivative bound gives local error `(2π/3) M r⁴`.

Circle requirement (approved direct-family route): `CircleLatticeRegularity` exports
`abs_iteratedDerivWithin_five_circleLatticeDualPhase_bounds`. For `R,h>0`,
`h≤Y` and `Y≤ν≤2Y`, the fifth derivative of the **integer-column** dual
`circleLatticeDualPhase R h ν = R*sqrt(h²+ν²)` has magnitude between
`R*h²/(125*Y⁶)` and `480*R*h²/Y⁶`. Global smoothness is proved. `CircleLegendre`
proves the actual critical point and Legendre identity for `h*sqrt(2Ru-u²)`.
The change `u=R-n` shifts the lattice; its Poisson factor cancels the linear
term `-Rν` in the uncorrected Legendre phase. These direct-family results do
not assert a small first-derivative perturbation for the full dual.
The weighted actual dual estimates and the direct-family source estimate
are now proved; see the exact counting interface below.

`StationaryTools` additionally exports the exact Schwartz-amplitude quadratic
Fourier identity `integral_schwartz_mul_quadratic`, with coefficient
`expPhase (1/8)/sqrt q`. This is checked independently of a bare improper
Fresnel integral or a general stationary-phase expansion.

Verification: targeted `nice -n 5 lake build WaveTurbulence.Foundations.VdCB.Basic` returned
`Build completed successfully (3808 jobs).`, without warnings. The scratch consumer and
axiom probe `/home/scott/wt-scratch/bproc/BasicAxioms.lean` exited 0; its five checked exports
have only `[propext, Classical.choice, Quot.sound]`.

Additional checked analytic interfaces (import the named module):

- `TruncatedPoisson.norm_sum_sub_truncated_poisson_le` (declaration namespace
  remains `WaveTurbulence.VdCB`): natural endpoints `a≤b`, global C² phase,
  actual `0≤f'≤N` and `f''≥0` on `[a,b]`. The half-open source sum minus the
  actual integrals for `ν∈Icc 0 N` is bounded by
  `(2*(1+log N)+4*log(N+1))/(2*pi)+1`.
- `SharpStationary.norm_integral_stationary_sub_main_le`: global C³ phase,
  actual `f'(c)=0`, `f''≥μ>0` on `[a,b]`, a central interval `[c-r,c+r]`
  contained in `[a,b]`, and `|f'''|≤M` there. The main term is
  `e(f(c)+1/8)/sqrt(f''(c))`; the error is
  `(2*pi/3)*M*r^4 + 2/(pi*f''(c)*r) + 2/(pi*μ*r)`.
- `SharpStationaryNegative.norm_integral_stationary_neg_sub_main_le`:
  the corresponding negative-curvature formula has `-1/8` and `sqrt(-f'')`.
- `BProcessFinite.norm_exponential_sum_sub_BProcess_le`: combines the sharp
  Poisson formula and stationary estimates for a finite set `S⊆Icc 0 N` of
  actual critical frequencies. Its nonstationary complement must have an
  actual derivative distance `ρ>0`. The error is the above Poisson error,
  `card(complement)/(pi*ρ)`, and the sum of the explicit stationary errors.
  This is an analytic finite B-process formula. **Analytic closure of
  `IsExponentPair` under `bTransform` remains unproved.**

These theorems currently assume global smoothness; the circle source phase
is smooth only on its open arc. Local source derivatives and localization
are proved separately by the localization modules. No global smoothness assertion for that
square-root phase is intended.

The circle localization and direct sharp stationary estimate are now proved:

- `CircleLocalization` supplies `circleSourceExtension` and proves global
  smoothness when `U>0` and `3U≤R`. It agrees on a neighborhood of every point
  of `[U,2U]` with `h*sqrt(2Ru-u²)`, preserving all actual derivatives.
- `CircleSourceBounds` gives the actual negative curvature between
  `h R² (4RU)^(-3/2)` and `h R² (RU)^(-3/2)` and the actual third derivative
  bound `3h R³ (RU)^(-5/2)` on the block.
- `CircleStationary.norm_integral_circlePhase_sub_main_le` applies the sharp
  negative-curvature stationary estimate to the original circle phase,
  using the explicit critical point. The radius must remain inside the block.
- `CircleColumnStationary.norm_integral_circleColumnPhase_sub_main_le`
  returns the same bound in the original column variable, with the corrected
  lattice dual `R*sqrt(h²+ν²)` and quarter phase `-1/8`.

Thus the approved direct-family option covers the circle's full multiplicative
arc factor, without a small-perturbation assumption. The optimized estimate
and counting interface are described below. General analytic closure of
`IsExponentPair` under B is not claimed.


## Completed direct circle-family B-process

Import `WaveTurbulence.Foundations.VdCB.CircleCountingBridge` (or `BProcess`).
All declaration names below are in `WaveTurbulence.VdCB`.

- `norm_sum_circle_endpoint_block_le`: for every real center `c`, radius
  `R≥1`, block scale `U≥1`, and natural harmonic `n>0`, the **actual** sum
  over `Counting.integerInterval (c-R) (c+R)`, filtered by
  `R/sqrt 2 < |x-c|`, `U < R-|x-c|`, and `R-|x-c| ≤ 2U`, is bounded by
  `circleEndpointConstant * n^(11/30) * R^(11/60) * U^(7/20)`.
  The phase is exactly `NumberTheory.expPhase (n * Counting.circleHeight R c x)`.
- `norm_sum_circle_endpoint_dyadic_le`: the exact `hblock` type consumed by
  `Counting.abs_card_latticeDisc_sub_area_le_of_endpoint_power_bounds`,
  specialized to `κ=11/30`, `λ=16/30`. It handles the exact strict block
  boundaries and any clipping by the octant cutoff.
- `abs_card_latticeDisc_sub_area_le`: unconditional uniform translated
  closed-disc discrepancy `≤ circleDiscrepancyConstant * R^(27/41)` for
  `R≥1`; the center carrier is `EuclideanSpace ℝ (Fin 2)`.
- `card_annulus_le`: unconditional annulus input with area term
  `6*pi*Q*rho` and error `3*circleDiscrepancyConstant*Q^(27/41)`, under
  `Q≥2`, `0<rho≤Q/4`, and actual lattice-point membership in that annulus.

`circleEndpointConstant = 2*(154618824001 + 16*pi)` is uniform in every
scale, center, harmonic and block. Constants are deliberately generous.
These are actual source sums, not conditional helpers assuming cancellation.
The proof consumes the landed fifth-derivative/A-process estimates of the
actual circle dual, then the negative-curvature B-process, and optimizes
all Poisson, omitted-frequency and stationary errors. Very short intervals
use the actual second-derivative test; very high harmonics use counting.

No assertion that the full circle factor lies in a small-perturbation
`HasPowerProfile` is used. The shared decreasing-power API remains available
with its proved trivial pair and coordinate transforms. Its **generic
analytic** A/B closure is outside this direct-family completion claim.
