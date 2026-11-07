/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.GoodOperationScalar
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleErasure
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ThreeLabelNormalization
import Mathlib.Tactic

/-! # Algebraic normalization of a local counting inequality

This conditional scalar helper is not a molecule counting proposition.
Its counting premise is supplied by the actual local deletion theorems.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp

 theorem good_normalization_of_count_bound
    {V D D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] (M : Molecule V D) (M' : Molecule V D')
    {d : ℕ} {L γ δ C1 C N gain : ℝ} {p j : ℕ}
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hC1 : 1 ≤ C1) (hC : 0 ≤ C) (hN : 1 ≤ N) (hp : p ≤ 3)
    (hgain : gain ≤ ((d : ℝ)-γ)*j)
    (hs : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hs' : ∀ a b, a ≠ b → M'.bondsBetween a b ≤ 1)
    (hj : M.circuitRank-M'.circuitRank = (j : ℤ))
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (D' → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ)
    (hc : countEFree M L γ δ (0 : Mom d) Adm ≤
      (⌈C*N^2*(δ⁻¹)^p*L^(((d : ℝ)-γ)*j-gain)⌉₊ : ℕ∞)*
        countEFree M' L γ δ (0 : Mom d) Adm') :
    countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal ((C+1)*N^2*(δ⁻¹)^3*L^(-gain))*
        countAFree M' L γ δ C1 (0 : Mom d) Adm' P := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hC1p : 0 < C1 := zero_lt_one.trans_le hC1
  have hlog0 : 0 < Real.log L^2 := by
    have hh : 0 < Real.log L := zero_lt_one.trans_le hlog
    positivity
  have hP : ∀ T ∈ ladderCells M, 0 ≤ P T := by
    rw [ladderCells_eq_empty_of_simple M hs]; simp
  have hP' : ∀ T ∈ ladderCells M', 0 ≤ P T := by
    rw [ladderCells_eq_empty_of_simple M' hs']; simp
  have hprod : cellProduct M L γ δ P = cellProduct M' L γ δ P := by
    rw [cellProduct_eq_one_of_simple M hs,cellProduct_eq_one_of_simple M' hs']
  have hh := countAFree_le_ratio_of_countEFree_le M M' L γ δ C1 (0 : Mom d)
    Adm Adm' P P _ hc
    (freeNormalization_pos M (d := d) (γ := γ) hLp hδ.1 hC1p hlog0 P hP).le
    (freeNormalization_pos M' (d := d) (γ := γ) hLp hδ.1 hC1p hlog0 P hP')
  have hr := freeNormalization_ratio_of_product_eq M M' (d := d) (γ := γ)
    hLp hδ.1 hC1p P hprod (by rw [cellProduct_eq_one_of_simple M' hs']; norm_num)
  rw [hj] at hr
  norm_num only [Int.cast_natCast, zpow_natCast] at hr
  have hB0 : 0 ≤ C1⁻¹*δ^(1/2 : ℝ) :=
    mul_nonneg (inv_nonneg.mpr hC1p.le) (Real.rpow_nonneg hδ.1.le _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 := by
    have hhalf : δ^(1/2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    have hi : C1⁻¹ ≤ 1 := (inv_le_one₀ hC1p).mpr hC1
    simpa only [one_mul] using mul_le_mul hi hhalf (Real.rpow_nonneg hδ.1.le _) zero_le_one
  have hscalar := good_operation_scalar_le hL hgain hN hδ hB0 hB1 hC hp
  have hn : (⌈C*N^2*(δ⁻¹)^p*L^(((d : ℝ)-γ)*j-gain)⌉₊ : ℝ)*
      freeNormalization M (d := d) L γ δ C1 P / freeNormalization M' (d := d) L γ δ C1 P ≤
      (C+1)*N^2*(δ⁻¹)^3*L^(-gain) := by
    rw [mul_div_assoc,hr]
    simpa only [neg_mul,mul_assoc] using hscalar
  exact hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hn) bot_le)

end WaveTurbulence.MoleProp
