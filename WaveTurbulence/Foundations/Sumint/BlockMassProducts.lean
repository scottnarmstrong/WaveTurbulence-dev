/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceFactorMasses
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Regrouping the exact independent masses into source blocks

The normal mass is present only for a true normal flag. All pair masses
are regrouped by their literal sigma index, so each distinguished linear
mass can be paired with the first bad pair or its normal triple.
-/

public section

open ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Insert a normal mass in its block, and the multiplicative identity otherwise. -/
@[expose] noncomputable def normalMassInBlock (S : SumintShape)
    (N : {i : Fin S.I // S.nor i = true} → ℝ≥0∞) (i : Fin S.I) : ℝ≥0∞ :=
  if hi : S.nor i = true then N ⟨i,hi⟩ else 1

/-- Extending by one preserves the literal product of normal source masses. -/
theorem prod_normalMassInBlock (S : SumintShape)
    (N : {i : Fin S.I // S.nor i = true} → ℝ≥0∞) :
    (∏ i : Fin S.I, normalMassInBlock S N i) = ∏ i, N i := by
  have htrue : (∏ i : {i : Fin S.I // S.nor i = true}, normalMassInBlock S N i) = ∏ i, N i := by
    apply Finset.prod_congr rfl
    intro i _
    exact dite_eq_left i.2
  have hfalse : (∏ i : {i : Fin S.I // ¬ S.nor i = true}, normalMassInBlock S N i) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact dite_eq_right i.2
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin S.I => S.nor i = true),htrue,hfalse,mul_one]

/-- Exact algebraic regrouping of the independent source masses into original blocks. -/
theorem prod_block_masses (S : SumintShape)
    (F : Fin S.I → ℝ≥0∞) (P : (Σ i : Fin S.I, Fin (S.m i)) → ℝ≥0∞)
    (N : {i : Fin S.I // S.nor i = true} → ℝ≥0∞) :
    (∏ i, F i)*(∏ a, P a)*(∏ i, N i) =
      ∏ i : Fin S.I, F i*(∏ j : Fin (S.m i), P ⟨i,j⟩)*normalMassInBlock S N i := by
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,prod_normalMassInBlock]
  rw [Fintype.prod_sigma]

/-- Every source block can be bounded after regrouping; no global conclusion is assumed. -/
theorem prod_masses_le_block_product (S : SumintShape)
    (F : Fin S.I → ℝ≥0∞) (P : (Σ i : Fin S.I, Fin (S.m i)) → ℝ≥0∞)
    (N : {i : Fin S.I // S.nor i = true} → ℝ≥0∞) (B : Fin S.I → ℝ≥0∞)
    (hB : ∀ i, F i*(∏ j : Fin (S.m i), P ⟨i,j⟩)*normalMassInBlock S N i ≤ B i) :
    (∏ i, F i)*(∏ a, P a)*(∏ i, N i) ≤ ∏ i, B i := by
  rw [prod_block_masses]
  exact Finset.prod_le_prod (fun i _ => hB i)

end WaveTurbulence.Sumint
