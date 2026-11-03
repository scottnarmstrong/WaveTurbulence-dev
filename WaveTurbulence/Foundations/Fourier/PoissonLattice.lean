/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Poisson summation on the scaled integer lattice

TARGET L1035, L1541, L1575. The lattice is `L⁻¹ ℤ`, and the Fourier
transform uses `exp(-2πi ξx)`. Scaling therefore gives the factor `L` and
frequencies `L m`, with no additional `2π` factors.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.Fourier

/-- Fourier scaling for a nonzero real dilation, in the paper's convention. -/
theorem fourier_comp_div (f : ℝ → ℂ) {L : ℝ} (hL : L ≠ 0) (ξ : ℝ) :
    𝓕 (fun x => f (x / L)) ξ = |L| • 𝓕 f (L * ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq,
    ← MeasureTheory.Measure.integral_comp_div]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have he : -(x * ξ) = -(x / L * (L * ξ)) := by field_simp
    dsimp only
    rw [he]

/-- Pullback by the lattice dilation preserves Schwartz functions. -/
@[expose] noncomputable def schwartzDilate {L : ℝ} (hL : L ≠ 0) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ L⁻¹ (inv_ne_zero hL)).toContinuousLinearEquiv f

@[simp] theorem schwartzDilate_apply {L : ℝ} (hL : L ≠ 0) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzDilate hL f x = f (x / L) := by
  simp [schwartzDilate, div_eq_mul_inv, mul_comm]

/-- TARGET L1035, L1541, L1575: Poisson summation on `L⁻¹ ℤ`. -/
theorem poisson_scaled (f : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 < L) :
    (∑' n : ℤ, f ((n : ℝ) / L)) = (L : ℂ) * ∑' m : ℤ, 𝓕 f (L * m) := by
  have h := (schwartzDilate hL.ne' f).tsum_eq_tsum_fourier 0
  simp only [zero_add, schwartzDilate_apply] at h
  have hf : (schwartzDilate hL.ne' f : ℝ → ℂ) = fun x => f (x / L) := by
    funext x
    exact schwartzDilate_apply _ _ _
  simp only [SchwartzMap.fourier_coe] at h
  rw [hf] at h
  simp_rw [fourier_comp_div f hL.ne', abs_of_pos hL] at h
  simpa only [AddCircle.coe_zero, fourier_eval_zero, mul_one, Complex.real_smul, tsum_mul_left, SchwartzMap.fourier_coe] using h

end WaveTurbulence.Fourier
