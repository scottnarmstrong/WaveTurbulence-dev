/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFiveDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairNormalization
import Mathlib.Tactic

/-! # Full normalized affected three/four-valent operation with three lost circuits

The genuine five-label source count absorbs the single lost ladder-position
weight using its gamma-zero saving. No local count or deviation estimate
is an input to this source branch theorem.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp

theorem operation_b_three_four_three_circuits_normalized_bound (d : ℕ) (hd : 3 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
      a ≠ b → M.deg a = 3 → M.deg b = 4 → M.bondsBetween a b = 2 →
    ∀ S ∈ ladderCells M, a ∈ S →
      (Degen.eraseAtoms M {a,b}).circuitRank = M.circuitRank-3 →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ T ∈ ladderCells M, 0 ≤ P T) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) P := by
  classical
  obtain ⟨C,R,hC,hCount⟩ := double_pair_three_four_five_count_bound d hd γ hγ
  let g := min γ (1-γ)
  have hg : 0 < g := lt_min hγ.1 (by linarith only [hγ.2])
  refine ⟨1,le_rfl,?_⟩
  intro C1 hC1 δ hδ
  refine ⟨max (max R 1) (((C+1)*δ⁻¹^2*(4/g)^2)^(2/g)),?_⟩
  intro L hL hlog V D _ _ _ M hM a ha b hb hab ha3 hb4 hdouble S hS haS hχ Adm P hP
  have hLR : R ≤ L := (le_max_left R 1).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right R 1).trans ((le_max_left _ _).trans hL)
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hC1p : 0 < C1 := zero_lt_one.trans_le hC1
  have hlog0 : 0 < Real.log L^2 := by have hh : 0 < Real.log L := zero_lt_one.trans_le hlog; positivity
  have hmeet : ¬Disjoint S {a,b} := fun h => disjoint_left.mp h haS (by simp)
  have hc := hCount L hLR δ hδ M hM a ha b hb hab ha3 hb4 hdouble S hS hmeet Adm
  have hpost := freeNormalization_pos (Degen.eraseAtoms M {a,b}) (d := d) (γ := γ)
    hLp hδ.1 hC1p hlog0 P (nonnegative_scales_erase M {a,b} P hP)
  have hh := countAFree_le_ratio_of_countEFree_le M (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d)
    Adm (erasedFreeAdmissibility M {a,b} Adm) P P _ hc
    (freeNormalization_pos M (d := d) (γ := γ) hLp hδ.1 hC1p hlog0 P hP).le hpost
  have hj : M.circuitRank-(Degen.eraseAtoms M {a,b}).circuitRank = 3 := by omega
  have hr := freeNormalization_double_pair_ratio M hM hab ha3 hdouble hS haS (d := d) (γ := γ)
    hLp hδ.1 hC1p hlog0 P hP
  rw [hj] at hr
  norm_num only [Int.cast_ofNat,zpow_ofNat] at hr
  have hB0 : 0 ≤ C1⁻¹*δ^(1/2 : ℝ) :=
    mul_nonneg (inv_nonneg.mpr hC1p.le) (Real.rpow_nonneg hδ.1.le _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 := by
    have hδhalf : δ^(1/2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    have hCinv : C1⁻¹ ≤ 1 := (inv_le_one₀ hC1p).mpr hC1
    simpa only [one_mul] using mul_le_mul hCinv hδhalf (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)
  have haExp : g ≤ (d : ℝ)-γ := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hgle : g ≤ γ := min_le_left _ _
    linarith only [hgle,hdR,hγ.2]
  have hs := five_label_deletion_scalar_le_one hL1 hg haExp hδ hB0 hB1 hC.le
    ((le_max_right _ _).trans hL)
  have hX : Molecule.ladderWeight L γ δ (P S) ≤ Real.log L^2 := min_le_left _ _
  have hcoef : 0 ≤ (⌈C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-g)⌉₊ : ℝ)*L^(-3*((d : ℝ)-γ))*(C1⁻¹*δ^(1/2 : ℝ))^3 := by positivity
  have hs' : (⌈C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℝ)*
      freeNormalization M (d := d) L γ δ C1 P /
      freeNormalization (Degen.eraseAtoms M {a,b}) (d := d) L γ δ C1 P ≤ 1 := by
    rw [mul_div_assoc,hr,show -((d : ℝ)-γ)*3 = -3*((d : ℝ)-γ) by ring]
    have hx := mul_le_mul_of_nonneg_left hX hcoef
    simpa only [g,mul_assoc] using hx.trans hs
  have he : ENNReal.ofReal ((⌈C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℝ)*
      freeNormalization M (d := d) L γ δ C1 P /
      freeNormalization (Degen.eraseAtoms M {a,b}) (d := d) L γ δ C1 P) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs'
  apply hh.trans
  calc
    _ ≤ 1*countAFree (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) P :=
      mul_le_mul_of_nonneg_right he bot_le
    _ = _ := one_mul _

end WaveTurbulence.MoleProp
