/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Positive normalization preserves the actual weighted coefficient mass -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped ENNReal

/-- The common scalar normalizer has exactly the original weighted mass
plus the fixed positive density's weighted mass, almost everywhere. -/
theorem exists_positive_weighted_envelope {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E w : X → ℝ≥0∞} (hE : Measurable E) (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (hfin : (∫⁻ x, w x*E x ∂μ) < ⊤)
    {g₀ : X → ℝ} (hg₀m : Measurable g₀) (hg₀i : Integrable g₀ μ) (hg₀p : ∀ x, 0 < g₀ x) :
    ∃ g : X → ℝ, Measurable g ∧ Integrable g μ ∧ (∀ x, 0 < g x) ∧
      (∀ᵐ x ∂μ, E x ≤ ENNReal.ofReal (g x)) ∧
      (∫⁻ x, w x*ENNReal.ofReal (g x) ∂μ) =
        (∫⁻ x, w x*E x ∂μ) + ∫⁻ x, w x*ENNReal.ofReal (g₀ x) ∂μ := by
  have hEfin : (∫⁻ x, E x ∂μ) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono (fun x => le_mul_of_one_le_left bot_le (hw1 x))) hfin
  have hi := integrable_toReal_of_lintegral_ne_top hE.aemeasurable hEfin.ne
  have htop := ae_lt_top hE hEfin.ne
  refine ⟨fun x => (E x).toReal+g₀ x,hE.ennreal_toReal.add hg₀m,hi.add hg₀i,
    fun x => add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg (hg₀p x),?_,?_⟩
  · filter_upwards [htop] with x hx
    calc E x = ENNReal.ofReal (E x).toReal := (ENNReal.ofReal_toReal hx.ne).symm
         _ ≤ ENNReal.ofReal ((E x).toReal+g₀ x) :=
           ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hg₀p x).le)
  · calc
      _ = ∫⁻ x, w x*(E x+ENNReal.ofReal (g₀ x)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [htop] with x hx
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (hg₀p x).le,ENNReal.ofReal_toReal hx.ne]
      _ = _ := by
        simp_rw [mul_add]
        exact lintegral_add_left (hw.mul hE) _

end WaveTurbulence.RegAsymp
