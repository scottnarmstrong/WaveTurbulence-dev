/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
/-! TARGET L2065–2067: only actually modified leaves pay the high-seminorm cost. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

theorem leaf_cost_product_le {ι : Type*} [DecidableEq ι] (s bad : Finset ι)
    (hbad : bad ⊆ s) (cost : ι → NNReal) (C₁ C₂ : ℝ)
    (hbound : ∀ i ∈ s, (cost i : ℝ) ≤ C₁ * (if i ∈ bad then C₂ else 1)) :
    (∏ i ∈ s, (cost i : ℝ)) ≤ C₁ ^ s.card * C₂ ^ bad.card := by
  classical
  have he : s.filter (fun i => i ∈ bad) = bad := by
    ext i
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hbad h, h⟩⟩
  calc
    _ ≤ ∏ i ∈ s, C₁ * (if i ∈ bad then C₂ else 1) :=
      prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) hbound
    _ = _ := by simp only [prod_mul_distrib, prod_const, prod_ite, he, one_pow, mul_one]

theorem card_modified_le_total_derivatives {ι : Type*} (s : Finset ι) (a : ι → ℕ) :
    (s.filter fun i => a i ≠ 0).card ≤ ∑ i ∈ s, a i := by
  classical
  calc
    _ = ∑ i ∈ s, if a i ≠ 0 then (1 : ℕ) else 0 := by
      rw [← sum_filter]
      simp
    _ ≤ _ := sum_le_sum fun i _ => by split_ifs <;> omega

/-- At most one chosen weight leaf per root, plus at most the total number of derivatives. -/
theorem card_weight_or_derivative_modified_le {ι : Type*} [DecidableEq ι]
    (s weights : Finset ι) (a : ι → ℕ) (w A : ℕ)
    (hw : weights.card ≤ w) (ha : (∑ i ∈ s, a i) ≤ A) :
    (weights ∪ s.filter (fun i => a i ≠ 0)).card ≤ w + A :=
  (card_union_le _ _).trans (Nat.add_le_add hw ((card_modified_le_total_derivatives s a).trans ha))

end WaveTurbulence.LGSpine
