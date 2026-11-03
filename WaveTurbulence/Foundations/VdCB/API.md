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
The B-transform/weight estimates are still in progress.

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
are being supplied separately. No global smoothness assertion for that
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

Thus the direct-family option covers the circle's full multiplicative arc
factor. Optimization, transformed weighted-sum estimates, and exponent-pair
closure are still separate outstanding work.
