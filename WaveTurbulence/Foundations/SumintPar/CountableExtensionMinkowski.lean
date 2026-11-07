/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.NormIntegralMinkowski
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Countable ambient-extension recombination in the drafted mixed norm

The extension is a counting integral. Its equality to the literal series
is proved wherever that series is summable, retaining pointwise agreement.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.SumintPar

/-- Summable absolute time masses give genuine counting-product integrability. -/
theorem integrable_count_prod_of_sum_mass {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {r : ℕ} (F : ι → (Fin r → ℝ) → ℂ)
    (hFm : ∀ j, Measurable (F j))
    (hF : (∑' j, ∫⁻ t, ‖F j t‖ₑ) < ⊤) :
    Integrable (fun q : ι × (Fin r → ℝ) => F q.1 q.2) (Measure.count.prod volume) := by
  have hm : Measurable (fun q : ι × (Fin r → ℝ) => F q.1 q.2) :=
    measurable_from_prod_countable_right hFm
  refine ⟨hm.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [lintegral_prod _ hm.enorm.aemeasurable,lintegral_count]
  exact hF

/-- Minkowski for the actual counting-integral ambient extension. -/
theorem XNorm00_count_integral_le {ι V : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Countable V] {r : ℕ} (θ : ℝ)
    (F : ι → (Fin r → ℝ) → V → ℂ)
    (hFm : ∀ j v, Measurable (fun t => F j t v))
    (hFi : ∀ j v, Integrable (fun t => F j t v))
    (hF : ∀ v, (∑' j, ∫⁻ t, ‖F j t v‖ₑ) < ⊤) :
    XNorm00 θ (fun t v => ∫ j, F j t v ∂Measure.count) ≤ ∑' j, XNorm00 θ (F j) := by
  have hm (v : V) : Measurable (fun q : ι × (Fin r → ℝ) => F q.1 q.2 v) :=
    measurable_from_prod_countable_right (fun j => hFm j v)
  exact (XNorm00_integral_le θ F hm
    (fun v => integrable_count_prod_of_sum_mass _ (fun j => hFm j v) (hF v)) hFi).trans_eq
      (lintegral_count _)

/-- At every point of summability the counting-integral extension is the literal series. -/
theorem count_integral_eq_tsum {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (f : ι → ℂ) (hf : Summable (fun j => ‖f j‖)) :
    (∫ j, f j ∂Measure.count) = ∑' j, f j := by
  have hi : Integrable f Measure.count := integrable_count_iff.mpr hf
  simpa [measureReal_def] using integral_countable hi

end WaveTurbulence.SumintPar
