/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Frozen.Defs.ProdDyadicCut
public import WaveTurbulence.Foundations.FC23.FrozenRadialBridge
/-! The exact per-tree T1/T2 decomposition and auxiliary leaf cutoff.
The leaf carrier here includes both signs; positive input representatives alone
are not sufficient for the conservation argument. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset Polynomial
variable {ι : Type*}

theorem product_difference_split (s t : Finset ι) (hd : Disjoint s t) (g h : ι → ℝ) :
    (∏ a ∈ s ∪ t, g a) - (∏ a ∈ s ∪ t, h a) =
      ((∏ a ∈ s, g a) - ∏ a ∈ s, h a) * (∏ a ∈ t, g a) +
      (∏ a ∈ s, h a) * ((∏ a ∈ t, g a) - ∏ a ∈ t, h a) := by
  rw [prod_union hd, prod_union hd]
  ring

/-- Literal D13 cutoff, including the predecessor scale in its frozen body. -/
theorem prodDyadicCut_split (L : ℝ) (j : ℕ) (s t : Finset ι)
    (hd : Disjoint s t) (y : ι → ℝ) :
    prodDyadicCut L (j + 1) (s ∪ t) y =
      ((∏ a ∈ s, chi0 (y a / (2 ^ (j + 1) * L))) -
        ∏ a ∈ s, chi0 (y a / (2 ^ j * L))) *
        (∏ a ∈ t, chi0 (y a / (2 ^ (j + 1) * L))) +
      (∏ a ∈ s, chi0 (y a / (2 ^ j * L))) *
        ((∏ a ∈ t, chi0 (y a / (2 ^ (j + 1) * L))) -
          ∏ a ∈ t, chi0 (y a / (2 ^ j * L))) := by
  simp only [prodDyadicCut, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, Nat.add_sub_cancel]
  exact product_difference_split s t hd _ _

def affineProduct (s : Finset ι) (g h : ι → ℂ) : ℂ[X] :=
  ∏ a ∈ s, (C (g a) + X * C (h a))

theorem affineProduct_eval (s : Finset ι) (g h : ι → ℂ) (z : ℂ) :
    (affineProduct s g h).eval z = ∏ a ∈ s, (g a + z * h a) := by
  simp only [affineProduct, eval_prod, eval_add, eval_C, eval_mul, eval_X]

theorem affineProduct_natDegree (s : Finset ι) (g h : ι → ℂ) :
    (affineProduct s g h).natDegree ≤ s.card := by
  apply (natDegree_prod_le _ _).trans
  calc
    (∑ a ∈ s, (C (g a) + X * C (h a)).natDegree) ≤ ∑ _a ∈ s, 1 := by
      apply sum_le_sum
      intro a _
      apply natDegree_add_le_of_degree_le
      · simp only [natDegree_C]; omega
      · exact (natDegree_mul_le).trans (by simp only [natDegree_X, natDegree_C]; omega)
    _ = s.card := by simp only [sum_const, smul_eq_mul, mul_one]

theorem affineProduct_difference (s : Finset ι) (g h : ι → ℂ) :
    (affineProduct s h (fun a => g a - h a)).eval 1 -
      (affineProduct s h (fun a => g a - h a)).eval 0 =
      (∏ a ∈ s, g a) - ∏ a ∈ s, h a := by
  simp only [affineProduct_eval, one_mul, add_sub_cancel, zero_mul, add_zero]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Conservation forces a large leaf of either sign in the same subtree. -/
theorem exists_large_leaf (s : Finset ι) (k : ι → V) (ε : ι → ℝ)
    (hε : ∀ a ∈ s, |ε a| ≤ 1) {r : V} (hr : r = ∑ a ∈ s, ε a • k a)
    {M : ℝ} (hlarge : (s.card : ℝ) * M < ‖r‖) :
    ∃ a ∈ s, M < ‖k a‖ := by
  by_contra hn
  push Not at hn
  have hbound : ‖r‖ ≤ (s.card : ℝ) * M := by
    rw [hr]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _a ∈ s, M := by
        apply sum_le_sum
        intro a ha
        rw [norm_smul, Real.norm_eq_abs]
        exact ((mul_le_mul_of_nonneg_right (hε a ha) (norm_nonneg _)).trans_eq
          (one_mul _)).trans (hn a ha)
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  exact (not_lt_of_ge hbound) hlarge

/-- The auxiliary cutoff identity holds exactly, before any estimate. -/
theorem auxiliary_cutoff_identity (s : Finset ι) (k : ι → V) (ε : ι → ℝ)
    (hε : ∀ a ∈ s, |ε a| ≤ 1) {r : V} (hr : r = ∑ a ∈ s, ε a • k a)
    {M : ℝ} (hM : 0 < M) (hlarge : (s.card : ℝ) * M < ‖r‖) (T : ℝ) :
    T = T * (1 - ∏ a ∈ s, chi0 (‖k a‖ / M)) := by
  obtain ⟨a, ha, hka⟩ := exists_large_leaf s k ε hε hr hlarge
  have hz : chi0 (‖k a‖ / M) = 0 := by
    rw [frozen_chi0_eq]
    apply Fourier.chi0_eq_zero
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hM.le)]
    exact (one_le_div hM).mpr hka.le
  have hp : (∏ a ∈ s, chi0 (‖k a‖ / M)) = 0 := prod_eq_zero ha hz
  rw [hp, sub_zero, mul_one]

/-- The tail factor uses evaluation at -1, not +1. -/
theorem auxiliary_polynomial (s : Finset ι) (g : ι → ℂ) :
    1 - (∏ a ∈ s, g a) =
      (affineProduct s (fun _ => 1) (fun a => 1 - g a)).eval 0 -
        (affineProduct s (fun _ => 1) (fun a => 1 - g a)).eval (-1) := by
  simp only [affineProduct_eval, zero_mul, add_zero, prod_const_one, neg_one_mul,
    neg_sub]
  congr 1
  apply prod_congr rfl
  intro a _
  ring
end WaveTurbulence.FC23
