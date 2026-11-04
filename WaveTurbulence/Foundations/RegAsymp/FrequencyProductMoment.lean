/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.Products

/-! # A single frequency moment for a factorized finite density

The first moment of a sum of leaf frequencies is paid with one fixed
first-moment bound per leaf, independently of the number of leaves.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped ENNReal

/-- A sum of nonnegative first moments is bounded by their product weights. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) : 1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1+a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have h0 := ha i (Finset.mem_insert_self _ _)
    have hs : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hsum : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg hs
    have hb := mul_le_mul_of_nonneg_left (ih hs) (show 0 ≤ 1+a i by positivity)
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    nlinarith

/-- The full sum-frequency moment is controlled by the product of the
actual one-factor first moments. The empty finite family is included. -/
theorem lintegral_sum_frequency_moment_le {ι E : Type*} [Fintype ι]
    [MeasureSpace E]
    [SigmaFinite (volume : Measure E)]
    (w : E → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ ξ : ι → E, ENNReal.ofReal (1+∑ i, w (ξ i)) * ∏ i, f i (ξ i)) ≤
      ∏ i, ∫⁻ ξ : E, ENNReal.ofReal (1+w ξ) * f i ξ := by
  classical
  calc
    _ ≤ ∫⁻ ξ : ι → E, ∏ i, ENNReal.ofReal (1+w (ξ i)) * f i (ξ i) := by
      apply lintegral_mono
      intro ξ
      change ENNReal.ofReal (1+∑ i, w (ξ i)) * (∏ i, f i (ξ i)) ≤
        ∏ i, ENNReal.ofReal (1+w (ξ i)) * f i (ξ i)
      rw [Finset.prod_mul_distrib,← ENNReal.ofReal_prod_of_nonneg (fun i _ => by have := hw0 (ξ i); positivity)]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (one_add_sum_le_prod_one_add Finset.univ (fun i => w (ξ i)) (fun i _ => hw0 _))) le_rfl
    _ = _ := by
      exact ApproxNT.lintegral_fintype_prod_eq_prod (fun i ξ => ENNReal.ofReal (1+w ξ) * f i ξ)
        (fun i => (ENNReal.measurable_ofReal.comp (measurable_const.add hw)).mul (hf i))

end WaveTurbulence.RegAsymp
