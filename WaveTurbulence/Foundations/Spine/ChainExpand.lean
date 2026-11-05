/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! # Expanding a product of rung weights (S3b LADDER-DECAY)

Pure algebra: the product over rungs of a finite signed sum of terms is the sum over all choices. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset

variable {n : ℕ} {P : Type*} {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma prod_sum_expand (a : Fin n → J → ℂ) :
    ∏ k, ∑ j, a k j = ∑ α : Fin n → J, ∏ k, a k (α k) := by
  exact Fintype.prod_sum a

omit [DecidableEq J] in
/-- The expansion of the constrained rung sum into choices of one term per rung. -/
lemma expand_rung_sum {Pt : Type*} (SP : Fin n → Finset Pt) (cond : (Fin n → Pt) → Prop) [DecidablePred cond]
    (Φ : (Fin n → Pt) → ℂ) (s : Fin n → J → ℝ) (χ : Fin n → J → Pt → ℝ) (ph : Fin n → Pt → ℂ)
    (cw : Fin n → Pt → ℂ) (hcut : ∀ Q, Φ Q ≠ 0 → ∀ k, cw k (Q k) = 1) :
    ∑ Q ∈ Fintype.piFinset SP, (if cond Q then
        Φ Q * ∏ k, (((∑ j, s k j * χ k j (Q k) : ℝ) : ℂ) * ph k (Q k)) else 0) =
      ∑ α : Fin n → J, (∏ k, ((s k (α k) : ℝ) : ℂ)) *
        ∑ Q ∈ Fintype.piFinset SP, (if cond Q then
          Φ Q * ∏ k, (((χ k (α k) (Q k) : ℝ) : ℂ) * cw k (Q k) * ph k (Q k)) else 0) := by
  have hpt : ∀ Q : Fin n → Pt, (if cond Q then
        Φ Q * ∏ k, (((∑ j, s k j * χ k j (Q k) : ℝ) : ℂ) * ph k (Q k)) else 0) =
      ∑ α : Fin n → J, (∏ k, ((s k (α k) : ℝ) : ℂ)) * (if cond Q then
          Φ Q * ∏ k, (((χ k (α k) (Q k) : ℝ) : ℂ) * cw k (Q k) * ph k (Q k)) else 0) := by
    intro Q
    by_cases hc : cond Q
    · simp only [hc, ite_true]
      by_cases hΦ : Φ Q = 0
      · simp [hΦ]
      · have hcw := hcut Q hΦ
        simp only [hcw, mul_one]
        have : ∏ k, (((∑ j, s k j * χ k j (Q k) : ℝ) : ℂ) * ph k (Q k)) =
            ∑ α : Fin n → J, ∏ k, (((s k (α k) : ℝ) : ℂ) * (((χ k (α k) (Q k) : ℝ) : ℂ) * ph k (Q k))) := by
          rw [← prod_sum_expand (fun k j => ((s k j : ℝ) : ℂ) * (((χ k j (Q k) : ℝ) : ℂ) * ph k (Q k)))]
          refine Finset.prod_congr rfl (fun k _ => ?_)
          push_cast
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => by ring)
        rw [this, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [Finset.prod_mul_distrib]; ring
    · simp [hc]
  rw [Finset.sum_congr rfl (fun Q _ => hpt Q), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [← Finset.mul_sum]

end WaveTurbulence.LadderDecay
