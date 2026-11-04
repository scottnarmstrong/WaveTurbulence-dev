/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Resonant.PVDecayOneDim

/-! # Scale-uniform principal-value bounds without compact support -/

public section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace WaveTurbulence.Resonant
namespace IsPVCutoff

theorem abs_pvTruncation_le_l1 {χ f : ℝ → ℝ} {K : ℝ≥0} {C : ℝ}
    (hχ : IsPVCutoff χ) (hf : Integrable f) (hL : LipschitzWith K f)
    (hC : ∀ u, |χ u| ≤ C) (μ : ℝ) :
    |pvTruncation χ μ f| ≤ (1+C)*(2*K+∫ u, |f u|) := by
  have hCn : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hi := integrable_pvQuotient_of_lipschitz hf hL
  rw [hχ.pvTruncation_eq_of_integrable hf μ,← Real.norm_eq_abs]
  have hh : ‖∫ u, (1-χ (μ*u))*pvQuotient f u‖ ≤ (1+C)*∫ u, |pvQuotient f u| := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hi.abs.const_mul _)
    apply Eventually.of_forall
    intro u
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact (abs_sub _ _).trans (by simpa only [abs_one] using add_le_add (le_refl (1 : ℝ)) (hC (μ*u)))
  exact hh.trans (mul_le_mul_of_nonneg_left (integral_abs_pvQuotient_le_l1 hf hL) (by linarith only [hCn]))

end IsPVCutoff
end WaveTurbulence.Resonant
