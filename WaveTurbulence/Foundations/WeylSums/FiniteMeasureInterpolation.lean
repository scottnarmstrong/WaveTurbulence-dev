/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Quantitative lower moments on a finite measure space -/

public section
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.WeylSums

/-- Hölder interpolation from the first moment to a smaller positive power,
with an explicit upper bound on the measure of the ambient space. -/
theorem integral_small_power_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) (hfi : Integrable f μ)
    (θ V : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hV : 0 ≤ V)
    (hμ : μ Set.univ ≤ ENNReal.ofReal V) :
    Integrable (fun x => f x^θ) μ ∧
      (∫ x, f x^θ ∂μ) ≤ (∫ x, f x ∂μ)^θ*V^(1-θ) := by
  have hpq : (1/θ).HolderConjugate (1/(1-θ)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (one_lt_div hθ.1).mpr hθ.2
    · field_simp [hθ.1.ne',sub_ne_zero.mpr hθ.2.ne']
      ring
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    ((hf.ennreal_ofReal).pow_const θ).aemeasurable (measurable_const.aemeasurable : AEMeasurable (fun _ : X => (1 : ℝ≥0∞)) μ)
  have hθid : θ*(1/θ) = 1 := by field_simp [hθ.1.ne']
  simp only [Pi.mul_apply,mul_one,← ENNReal.rpow_mul, hθid, ENNReal.rpow_one, ENNReal.one_rpow,
    one_div_one_div, lintegral_const, one_mul] at hh
  have hIf : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hfn
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hfn)] at hh
  have hmup : (μ Set.univ)^(1-θ) ≤ (ENNReal.ofReal V)^(1-θ) :=
    ENNReal.rpow_le_rpow hμ (by linarith only [hθ.2])
  have hl : (∫⁻ x, ENNReal.ofReal (f x^θ) ∂μ) ≤
      ENNReal.ofReal ((∫ x, f x ∂μ)^θ*V^(1-θ)) := by
    simp_rw [← ENNReal.ofReal_rpow_of_nonneg (hfn _) hθ.1.le]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hIf _),
      ← ENNReal.ofReal_rpow_of_nonneg hIf hθ.1.le,
      ← ENNReal.ofReal_rpow_of_nonneg hV (by linarith only [hθ.2])]
    exact hh.trans (mul_le_mul le_rfl hmup (by positivity) (by positivity))
  have hnonneg (x : X) : 0 ≤ f x^θ := Real.rpow_nonneg (hfn x) _
  have hi : Integrable (fun x => f x^θ) μ :=
    ⟨(hf.pow_const θ).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)).mpr
        (hl.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg hIf _) (Real.rpow_nonneg hV _))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg)]
  exact hl

end WaveTurbulence.WeylSums
