# Packet TORUS-FOURIER — Fourier series on the torus 𝕋_L^d = [0, L]^d

Read `COMMON.md` (same directory) first.
Worktree: `/home/scott/WaveTurbulence-worktrees/torus-fourier`, branch `w/torus-fourier`.
Files you own: `WaveTurbulence/Foundations/Torus/**`.

## Context

TARGET (`/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`, L277–L330, (1.2) `fourier`)
works with smooth solutions of cubic NLS on `𝕋_L^d` and their Fourier coefficients `û(t,k)`, `k ∈ ℤ_L^d = (L⁻¹ℤ)^d`;
the reduction to the Fourier-side system `a_k(t)` is at L540–L566. This packet builds the Fourier analysis the NLS
part needs. Physical space is `Fin d → ℝ`; lattice points are `n : Fin d → ℤ` with `k = n / L`; `L > 0` real.

## DRAFT definition (verbatim; namespace `WaveTurbulence`, `open MeasureTheory Complex Set`)

```lean
/-- The space Fourier coefficient (DH (1.2)):
`f̂(k) = L^{-d/2} ∫_{[0,L]^d} f(x) e^{-2πi k·x} dx` at `k = n / L ∈ ℤ_L^d`. -/
def torusFourierCoeff {d : ℕ} (L : ℝ) (f : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
    ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L),
      f x * exp (-(2 * Real.pi * ∑ j, (n j : ℝ) / L * x j : ℝ) * I)
```

## Goal (in this order; commit after each)

For `L > 0` and `f : (Fin d → ℝ) → ℂ` that is `L`-periodic in each coordinate (`f (x + Pi.single j L) = f x`):
1. Bridge to Mathlib's Fourier theory on `UnitAddTorus`/`AddCircle` (rescaling `x ↦ x / L`), so its results transfer.
2. Smooth (`ContDiff ℝ ⊤`) periodic `f` ⇒ coefficients decay faster than any power: `∀ N, ∃ C, ‖f̂(n)‖ ≤ C (1+‖n‖)^{-N}`.
   Conversely, rapidly decaying coefficients `c : (Fin d → ℤ) → ℂ` define a smooth periodic function
   `L^{-d/2} ∑ c(n) e^{2πi (n/L)·x}` whose coefficients are `c`.
3. Inversion: smooth periodic `f` equals its absolutely convergent Fourier series. Uniqueness: two continuous periodic
   functions with equal coefficients are equal.
4. Parseval: `∑ |f̂(n)|² = ∫_{[0,L]^d} |f|²` (for continuous periodic `f`, or `L²`).
5. Derivatives and products: coefficients of `∂_j f` are `2πi (n_j/L) f̂(n)`; of the normalized Laplacian
   `(2π)⁻¹ ∑ ∂_j² f` are `-2π |n/L|² f̂(n)`; of `f g` and `f ḡ` are the discrete convolutions with the factor
   `L^{-d/2}`; the coefficients of `|f|² f` in terms of `f̂` (cubic convolution over `n₁ − n₂ + n₃ = n`).
   Use `partialDeriv j f x = deriv (fun r => f (Function.update x j r)) (x j)` as the partial derivative.
6. Time-dependent version: for `u` that is `C^∞` on `[0,T] × ℝ^d` and periodic, `t ↦ û(t, n)` is differentiable on
   `[0,T]` with derivative the coefficient of `∂_t u`.

Mine Mathlib (`Mathlib/Analysis/Fourier/AddCircleMulti.lean`, `UnitAddTorus`, `mFourier`, `fourierCoeff`) and Scott's
repos (NavierStokesAndEuler, Superdiffusion, KPZ "Phi4/Fourier", Critical2DKPZ, Frohlich-Spencer) first.

## Stop conditions

Done: `READY torus-fourier`. Blocked > ~1 hour on one ingredient: `STOPPED torus-fourier: <reason>`.
