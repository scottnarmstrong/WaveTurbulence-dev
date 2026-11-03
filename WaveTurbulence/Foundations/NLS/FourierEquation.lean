/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Torus.TimeDerivative
public import WaveTurbulence.Foundations.Torus.Product
public import WaveTurbulence.Frozen.Defs.LatticePoint

/-!
# The Fourier-side form of (NLS)

For a smooth solution `u` of (NLS) `(i∂ₜ - Δ)u + α|u|²u = 0` on `𝕋_L^d` (TARGET L278–L283,
the frozen `IsSmoothNLSSolution`), the coefficients `û(t, n) = torusFourierCoeff L (u t) n` of
TARGET (1.2) satisfy on `[0, T]` (one-sided at the endpoints)

`∂ₜ û(t, n) = i (2π |k|² û(t, n) + α L^{-d} ∑_{n₁ - n₂ + n₃ = n} û(t,n₁) conj û(t,n₂) û(t,n₃))`,

`k = n / L = latticePoint L n` (`IsSmoothNLSSolution.hasDerivWithinAt_torusFourierCoeff_eq`). The
cubic sum is `cubicConv L b n`, parametrized by `(n₁, n₂)` with `n₃ = n - n₁ + n₂`, and converges
absolutely (`hasSum_cubicConv`).
-/

public section

noncomputable section

open MeasureTheory Complex Set
open scoped ContDiff

namespace WaveTurbulence

variable {d : ℕ}

/-- The cubic convolution `L^{-d} ∑_{n₁ - n₂ + n₃ = n} b(n₁) conj b(n₂) b(n₃)`, parametrized by
`(n₁, n₂)` (`n₃ = n - n₁ + n₂`): the coefficient of `|u|²u` in terms of `b = û`
(TARGET L278, L286). -/
@[expose] def cubicConv (L : ℝ) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  ((L ^ d : ℝ) : ℂ)⁻¹ *
    ∑' p : (Fin d → ℤ) × (Fin d → ℤ), b p.1 * (starRingEnd ℂ) (b p.2) * b (n - p.1 + p.2)

theorem norm_latticePoint_sq (L : ℝ) (n : Fin d → ℤ) :
    ‖latticePoint L n‖ ^ 2 = ∑ j, ((n j : ℝ) / L) ^ 2 := by
  simp [latticePoint, EuclideanSpace.norm_sq_eq, div_pow, sq_abs]

/-- For smooth periodic `f`, `(|f|² f)^(n) = cubicConv L f̂ n`, an absolutely convergent sum. -/
theorem hasSum_cubicConv {L : ℝ} (hL : 0 < L) {f : (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsTorusPeriodic L f) (n : Fin d → ℤ) :
    HasSum (fun p : (Fin d → ℤ) × (Fin d → ℤ) => ((L ^ d : ℝ) : ℂ)⁻¹ *
        (torusFourierCoeff L f p.1 * (starRingEnd ℂ) (torusFourierCoeff L f p.2) *
          torusFourierCoeff L f (n - p.1 + p.2)))
      (cubicConv L (torusFourierCoeff L f) n) := by
  have h := hasSum_torusFourierCoeff_normSq_mul hL hf hp n
  rw [cubicConv, ← tsum_mul_left, h.tsum_eq]
  exact h

theorem cubicConv_torusFourierCoeff {L : ℝ} (hL : 0 < L) {f : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : IsTorusPeriodic L f) (n : Fin d → ℤ) :
    cubicConv L (torusFourierCoeff L f) n =
      torusFourierCoeff L (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) * f x) n :=
  (hasSum_cubicConv hL hf hp n).unique (hasSum_torusFourierCoeff_normSq_mul hL hf hp n)

theorem continuous_normLaplacian {f : (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ 2 f) :
    Continuous (normLaplacian f) := by
  have h1 : ∀ j, ContDiff ℝ 1 (partialDeriv j f) := fun j =>
    contDiff_partialDeriv (n := 1) (by norm_num; exact hf) j
  exact continuous_const.mul
    (continuous_finsetSum _ fun j _ => continuous_partialDeriv (h1 j) j)

/-- The coefficients of the normalized Laplacian in terms of `|k|² = ‖latticePoint L n‖²`. -/
theorem torusFourierCoeff_normLaplacian' {L : ℝ} (hL : 0 < L) {f : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ 2 f) (hp : IsTorusPeriodic L f) (n : Fin d → ℤ) :
    torusFourierCoeff L (normLaplacian f) n =
      -((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ) * torusFourierCoeff L f n := by
  rw [torusFourierCoeff_normLaplacian hL hf hp, norm_latticePoint_sq]

/-- (NLS) solved for the time derivative: `∂ₜ u = -i (Δu - α|u|²u)` on `[0, T]`. -/
theorem IsSmoothNLSSolution.derivWithin_eq {L α T : ℝ} {c : (Fin d → ℤ) → ℂ}
    {u : ℝ → (Fin d → ℝ) → ℂ} (hu : IsSmoothNLSSolution L α T c u) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : Fin d → ℝ) :
    derivWithin (fun s => u s x) (Icc 0 T) t =
      -I * (normLaplacian (u t) x - (α : ℂ) * (((‖u t x‖ ^ 2 : ℝ) : ℂ) * u t x)) := by
  have h := hu.2.2.2 t ht x
  linear_combination (-I) * h + (derivWithin (fun s => u s x) (Icc 0 T) t) * I_sq

/-- **The Fourier-side equation** (TARGET L278–L286, L540–L566): for a smooth solution of (NLS)
with `L > 0`, on `[0, T]`

`∂ₜ û(t, n) = i (2π |k|² û(t, n) + α L^{-d} ∑_{n₁ - n₂ + n₃ = n} û(t,n₁) conj û(t,n₂) û(t,n₃))`,

`k = latticePoint L n`, with the time derivative one-sided at `t = 0, T`. -/
theorem IsSmoothNLSSolution.hasDerivWithinAt_torusFourierCoeff_eq {L α T : ℝ}
    {c : (Fin d → ℤ) → ℂ} {u : ℝ → (Fin d → ℝ) → ℂ} (hL : 0 < L)
    (hu : IsSmoothNLSSolution L α T c u) {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    HasDerivWithinAt (fun s => torusFourierCoeff L (u s) n)
      (I * (((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ) * torusFourierCoeff L (u t) n +
        (α : ℂ) * cubicConv L (torusFourierCoeff L (u t)) n))
      (Icc 0 T) t := by
  have hd := hu.hasDerivWithinAt_torusFourierCoeff ht n
  have hsm : ContDiff ℝ ∞ (u t) := hu.contDiff ht
  have hper : IsTorusPeriodic L (u t) := hu.isTorusPeriodic ht
  have hc : Continuous (u t) := hsm.continuous
  have h2 : ContDiff ℝ 2 (u t) := hsm.of_le (by norm_cast)
  have hN : Continuous fun x => (α : ℂ) * (((‖u t x‖ ^ 2 : ℝ) : ℂ) * u t x) := by fun_prop
  convert hd using 1
  rw [funext (hu.derivWithin_eq ht), torusFourierCoeff_const_mul,
    torusFourierCoeff_sub (f := normLaplacian (u t))
      (g := fun x => (α : ℂ) * (((‖u t x‖ ^ 2 : ℝ) : ℂ) * u t x))
      (continuous_normLaplacian h2).integrableOn_Icc hN.integrableOn_Icc,
    torusFourierCoeff_const_mul, torusFourierCoeff_normLaplacian' hL h2 hper, cubicConv_torusFourierCoeff hL hsm hper]
  ring

end WaveTurbulence
