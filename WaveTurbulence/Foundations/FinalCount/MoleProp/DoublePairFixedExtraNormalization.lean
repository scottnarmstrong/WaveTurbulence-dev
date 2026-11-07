/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFixedExtraCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairNormalization
import Mathlib.Tactic

/-! # DH23 laddersharp for the actual degree-three/three affected pair -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp

theorem operation_b_three_four_fixed_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → (∀ x, M.atom x ≠ M.atom (M.mate x)) →
    ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ b → M.deg a = 3 → M.deg b = 4 → M.bondsBetween a b = 2 →
      (Degen.eraseAtoms M {a,b}).circuitRank = M.circuitRank - 2 →
    ∀ S ∈ ladderCells M, a ∈ S →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → CellGapRestriction M L (0 : Mom d) P (GapScale L) κ) →
      (∀ T ∈ ladderCells M, 0 ≤ P T) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) P := by
  classical
  obtain ⟨C,hC,hCount⟩ := double_pair_three_four_fixed_count_bound d hd γ hγ
  refine ⟨C+1,by linarith only [hC],?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hCount δ hδ
  refine ⟨max R 1,?_⟩
  intro L hL hlog V D _ _ _ M hM hloop a ha b hb hab ha3 hb4 hdouble hloss S hS haS Adm P hGap hP
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hC1p : 0 < C1 := by linarith only [hC,hC1]
  have hlog0 : 0 < Real.log L^2 := by have hh : 0 < Real.log L := zero_lt_one.trans_le hlog; positivity
  have haExp : 1 ≤ (d : ℝ)-γ := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hdR,hγ.2]
  have hc := hR L ((le_max_left R 1).trans hL) M hM hloop a ha b hb hab ha3 hb4 hdouble hloss S hS haS Adm P hGap
  have hpost := freeNormalization_pos (Degen.eraseAtoms M {a,b}) (d := d) (γ := γ)
    hLp hδ.1 hC1p hlog0 P (nonnegative_scales_erase M {a,b} P hP)
  have hh := countAFree_le_ratio_of_countEFree_le M (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d)
    Adm (erasedFreeAdmissibility M {a,b} Adm) P P _ hc
    (freeNormalization_pos M (d := d) (γ := γ) hLp hδ.1 hC1p hlog0 P hP).le hpost
  have hmeet : ¬ Disjoint S {a,b} := fun h => disjoint_left.mp h haS (by simp)
  have hj : M.circuitRank-(Degen.eraseAtoms M {a,b}).circuitRank = 2 := by omega
  have hr := freeNormalization_double_pair_ratio M hM hab ha3 hdouble hS haS (d := d) (γ := γ)
    hLp hδ.1 hC1p hlog0 P hP
  rw [hj] at hr
  norm_num only [Int.cast_ofNat,zpow_ofNat] at hr
  have hX : 1 ≤ Molecule.ladderWeight L γ δ (P S) := ladderWeight_one_le hLp.le hlog hδ.1.le (hP S hS)
  have hXlog : Molecule.ladderWeight L γ δ (P S) ≤ Real.log L^2 := min_le_left _ _
  have hlarge : C+1 ≤ C1^2 := by nlinarith only [hC,hC1]
  have hs := four_label_deletion_scalar_le_one hL1 haExp hδ hC1p hC.le hlarge hX hXlog
  have hs' : (⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))*(Molecule.ladderWeight L γ δ (P S))⁻¹⌉₊ : ℝ)*
      freeNormalization M (d := d) L γ δ C1 P / freeNormalization (Degen.eraseAtoms M {a,b}) (d := d) L γ δ C1 P ≤ 1 := by
    rw [mul_div_assoc,hr,show -((d : ℝ)-γ)*2 = -2*((d : ℝ)-γ) by ring]
    simpa only [mul_assoc] using hs
  have he : ENNReal.ofReal ((⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))*(Molecule.ladderWeight L γ δ (P S))⁻¹⌉₊ : ℝ)*
      freeNormalization M (d := d) L γ δ C1 P / freeNormalization (Degen.eraseAtoms M {a,b}) (d := d) L γ δ C1 P) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs'
  apply hh.trans
  calc
    _ ≤ 1*countAFree (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) P :=
      mul_le_mul_of_nonneg_right he bot_le
    _ = _ := one_mul _

end WaveTurbulence.MoleProp
