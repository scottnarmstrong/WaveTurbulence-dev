/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueEstimates
public import WaveTurbulence.Foundations.Resonant.BilinearFourierLimit

/-!
# Matching the energy and bilinear principal-value normalizations

The collision energy is `-2⟨ℓ,x⟩`; DH21 Lemma 6.3 uses `⟨ℓ,x⟩` on the square
torus. Evenness of the cutoff gives the exact factor `-1/2` and scale `2μ`.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- Exact normalization bridge at every finite scale, before taking principal values. -/
theorem energyInvIntegral_eq_bilinearFourierTruncation
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ) (F : Mom d → Mom d → ℝ) :
    (energyInvIntegral χ μ F : ℂ) = -(2 : ℂ)⁻¹ *
      bilinearFourierTruncation χ (2 * μ) (fun ℓ x => (F ℓ x : ℂ)) 0 0 := by
  have hq : ∀ r : ℝ, (1 - χ (μ * (-(2 * r)))) / (-(2 * r)) =
      -(2 : ℝ)⁻¹ * ((1 - χ ((2 * μ) * r)) / r) := by
    intro r
    rw [mul_neg, hχ.even]
    have he : μ * (2 * r) = (2 * μ) * r := by ring
    rw [he]
    simp only [div_eq_mul_inv, inv_neg, mul_inv]
    ring
  rw [energyInvIntegral, ← integral_complex_ofReal, bilinearFourierTruncation, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ℓ => ?_)
  simp only [inner_zero_left, unitPhase, one_mul, zero_mul, Complex.ofReal_zero, Complex.exp_zero]
  rw [energyInvInner, ← integral_complex_ofReal, bilinearInvFourierInner, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inner_zero_left, unitPhase, one_mul, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    hq, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

/-- Principal-value energy convergence from the localized bilinear theorem. -/
theorem tendsto_energyInvIntegral_localized
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hR : 1 ≤ R)
    {F : Mom d → Mom d → ℝ} {a b : Mom d} (hc : Continuous (Function.uncurry F))
    (hL : ∀ x, LipschitzWith D (F x)) (hb : ∀ x y, |F x y| ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → F x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → F x y = 0) :
    Tendsto (fun μ => (energyInvIntegral χ μ F : ℂ)) atTop
      (𝓝 (-(2 : ℂ)⁻¹ * bilinearFourierLimitFormula (fun x y => (F x y : ℂ)) 0 0)) := by
  have hA : Continuous (Function.uncurry (fun x y => (F x y : ℂ))) := Complex.continuous_ofReal.comp hc
  have hAL : ∀ x, LipschitzWith D (fun y => (F x y : ℂ)) := by
    intro x
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp (hL x)
  have hAb : ∀ x y, ‖(F x y : ℂ)‖ ≤ D := fun x y => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb x y
  have hAx : ∀ x y, R < ‖x - a‖ → (F x y : ℂ) = 0 := fun x y h => by rw [hsx x y h]; rfl
  have hAy : ∀ x y, R < ‖y - b‖ → (F x y : ℂ) = 0 := fun x y h => by rw [hsy x y h]; rfl
  have ht := tendsto_bilinearFourierTruncation hd hχ hχs hC hR hA hAL hAb hAx hAy 0 0
  have hscale : Tendsto (fun μ : ℝ => 2 * μ) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  exact ((ht.comp hscale).const_mul (-(2 : ℂ)⁻¹)).congr fun μ =>
    (energyInvIntegral_eq_bilinearFourierTruncation hχ μ F).symm

end WaveTurbulence.Resonant
