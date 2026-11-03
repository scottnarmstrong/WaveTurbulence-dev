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

Circle requirement: the generic power profile is not asserted to contain all circle blocks
with arbitrarily small perturbation. The approved direct-family option is being implemented
using dual phase `R(sqrt(h²+ν²)-ν)` and its uniformly nonzero fifth derivative on `ν≥h>0`.
Its derivative calculation and subsequent B-transform/weight estimates are still in progress.

Verification: targeted `nice -n 5 lake build WaveTurbulence.Foundations.VdCB.Basic` returned
`Build completed successfully (3808 jobs).`, without warnings. The scratch consumer and
axiom probe `/home/scott/wt-scratch/bproc/BasicAxioms.lean` exited 0; its five checked exports
have only `[propext, Classical.choice, Quot.sound]`.
