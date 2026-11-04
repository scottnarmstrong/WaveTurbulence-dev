/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # A positive scalar normalization from a finite common coefficient envelope -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped ENNReal

/-- Adding one fixed positive integrable density makes the common symbol
normalization everywhere positive, without losing its quantitative mass. -/
theorem exists_positive_integrable_envelope {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E : X → ℝ≥0∞} (hE : Measurable E) (hfin : (∫⁻ x, E x ∂μ) < ⊤)
    {g₀ : X → ℝ} (hg₀m : Measurable g₀) (hg₀i : Integrable g₀ μ) (hg₀p : ∀ x, 0 < g₀ x) :
    ∃ g : X → ℝ, Measurable g ∧ Integrable g μ ∧ (∀ x, 0 < g x) ∧
      (∀ᵐ x ∂μ, E x ≤ ENNReal.ofReal (g x)) ∧
      (∫ x, g x ∂μ) = (∫⁻ x, E x ∂μ).toReal + ∫ x, g₀ x ∂μ := by
  have hi := integrable_toReal_of_lintegral_ne_top hE.aemeasurable hfin.ne
  have htop := ae_lt_top hE hfin.ne
  refine ⟨fun x => (E x).toReal+g₀ x,hE.ennreal_toReal.add hg₀m,hi.add hg₀i,
    fun x => add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg (hg₀p x),?_,?_⟩
  · filter_upwards [htop] with x hx
    calc E x = ENNReal.ofReal (E x).toReal := (ENNReal.ofReal_toReal hx.ne).symm
         _ ≤ ENNReal.ofReal ((E x).toReal+g₀ x) :=
           ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hg₀p x).le)
  · rw [integral_add hi hg₀i,integral_toReal hE.aemeasurable htop]

end WaveTurbulence.RegAsymp
