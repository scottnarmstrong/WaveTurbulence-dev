/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.EventChangeL2
/-! Conditional Cauchy–Schwarz with a pointwise small remainder multiplier, TARGET S6. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set

/-- A uniformly small multiplier retains its smallness after conditional integration; the
other factors are controlled by their old-event L2 moment, without normalizing either measure. -/
theorem norm_setIntegral_mul_le_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A B : Set Ω}
    (hB : MeasurableSet B) (hBA : B ⊆ A) {f g : Ω → ℂ}
    (hf : MemLp f 2 (μ.restrict A)) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ᵐ ω ∂μ.restrict B, ‖g ω‖ ≤ C) :
    ‖∫ ω in B, g ω * f ω ∂μ‖ ≤ C * Real.sqrt (∫ ω in A, ‖f ω‖ ^ 2 ∂μ) := by
  have hfB : MemLp f 2 (μ.restrict B) := hf.mono_measure (Measure.restrict_mono hBA le_rfl)
  have henv : Integrable (fun ω => C * ‖f ω‖) (μ.restrict B) :=
    (hfB.integrable (by norm_num)).norm.const_mul C
  have hnorm : ‖∫ ω in B, g ω * f ω ∂μ‖ ≤ ∫ ω in B, C * ‖f ω‖ ∂μ :=
    norm_integral_le_of_norm_le henv (hg.mono fun ω hω => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hω (norm_nonneg _))
  have hcs := Probability.norm_setIntegral_le_sqrt_measure_mul hf.norm B
  rw [Measure.restrict_restrict hB, Set.inter_eq_left.mpr hBA,
    measureReal_restrict_apply hB, Set.inter_eq_left.mpr hBA] at hcs
  simp_rw [Real.norm_of_nonneg (norm_nonneg _)] at hcs
  rw [Real.norm_of_nonneg (integral_nonneg (fun ω => norm_nonneg (f ω)))] at hcs
  have hp : Real.sqrt (μ.real B) ≤ 1 :=
    (Real.sqrt_le_sqrt (measureReal_le_one (μ := μ))).trans_eq Real.sqrt_one
  have hnormf : (∫ ω in B, ‖f ω‖ ∂μ) ≤ Real.sqrt (∫ ω in A, ‖f ω‖ ^ 2 ∂μ) :=
    hcs.trans (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg _)))
  rw [integral_const_mul] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left hnormf hC)

end WaveTurbulence.Induct
