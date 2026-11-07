/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.P101.OneLoss
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ThreeLabelNormalization
import Mathlib.Tactic

/-! # DH23 operation(a): full normalized one-circuit-loss branches -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.MoleProp

theorem countAFree_erase_one_circuit_at (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2)
    (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L → ∀ C1 ≥ (1 : ℝ),
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ v ∈ M.atoms,
    (M.deg v = 2 ∨ (M.deg v = 3 ∧ (Degen.newComponents M {v}).card = 2)) →
    (¬ ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2) →
    (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank-1 →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGapAt M v L γ η (0 : Mom d) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P := by
  classical
  obtain ⟨C,R,hC,hBound⟩ := one_loss_deletion_bound_at d hd γ hγ η hη hηmax
  refine ⟨max (max R 1) (((C+1)*δ⁻¹)^(η⁻¹)),?_⟩
  intro L hL hlog C1 hC1 V D _ _ _ M hM v hv hbranch hno hχ Adm P hAdm hP
  have hLR : R ≤ L := (le_max_left R 1).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right R 1).trans ((le_max_left _ _).trans hL)
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hC1p : 0 < C1 := zero_lt_one.trans_le hC1
  have hlog0 : 0 < Real.log L ^ 2 := by have hh : 0 < Real.log L := zero_lt_one.trans_le hlog; positivity
  have hdeg : M.deg v ≤ 3 := by rcases hbranch with h2 | ⟨h3,_⟩ <;> omega
  have hcells := ladderCells_erase_eq_of_no_operation_b M hM hv hdeg hno
  have hprod : cellProduct M L γ δ P = cellProduct (Degen.eraseAtoms M {v}) L γ δ P := by
    unfold cellProduct
    rw [hcells]
  have hPpost : ∀ S ∈ ladderCells (Degen.eraseAtoms M {v}), 0 ≤ P S := by rw [hcells]; exact hP
  have hpost := freeNormalization_pos (Degen.eraseAtoms M {v}) (d := d) (γ := γ) hL0 hδ.1 hC1p hlog0 P hPpost
  have hc := hBound L hLR δ hδ M hM v hv hbranch Adm hAdm
  have hh := countAFree_le_ratio_of_countEFree_le M (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d)
    Adm (erasedFreeAdmissibility M {v} Adm) P P _ hc
    (freeNormalization_pos M (d := d) (γ := γ) hL0 hδ.1 hC1p hlog0 P hP).le hpost
  have hj : M.circuitRank-(Degen.eraseAtoms M {v}).circuitRank = 1 := by omega
  have hr := freeNormalization_ratio_of_product_eq M (Degen.eraseAtoms M {v}) (d := d) (γ := γ)
    hL0 hδ.1 hC1p P hprod (cellProduct_pos (Degen.eraseAtoms M {v}) (γ := γ) hL0.le hδ.1.le hlog0 P hPpost)
  rw [hj] at hr
  norm_num only [Int.cast_one,zpow_one,mul_one] at hr
  have hB0 : 0 ≤ C1⁻¹*δ^(1/2 : ℝ) :=
    mul_nonneg (inv_nonneg.mpr hC1p.le) (Real.rpow_nonneg hδ.1.le _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 := by
    have hδhalf : δ^(1/2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    have hCinv : C1⁻¹ ≤ 1 := (inv_le_one₀ hC1p).mpr hC1
    simpa only [one_mul] using mul_le_mul hCinv hδhalf (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)
  have ha : η ≤ (d : ℝ)-γ := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hm := min_le_left γ (1-γ)
    linarith only [hηmax,hm,hdR,hγ.2]
  have hs := pair_deletion_scalar_le_one hL1 ha hη hδ hB0 hB1 hC ((le_max_right _ _).trans hL)
  have hs' : (⌈C*δ⁻¹*L^((d : ℝ)-γ-η)⌉₊ : ℝ)*freeNormalization M (d := d) L γ δ C1 P /
      freeNormalization (Degen.eraseAtoms M {v}) (d := d) L γ δ C1 P ≤ 1 := by
    rw [mul_div_assoc,hr]
    simpa only [mul_assoc] using hs
  have he : ENNReal.ofReal ((⌈C*δ⁻¹*L^((d : ℝ)-γ-η)⌉₊ : ℝ)*freeNormalization M (d := d) L γ δ C1 P /
      freeNormalization (Degen.eraseAtoms M {v}) (d := d) L γ δ C1 P) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs'
  apply hh.trans
  calc
    _ ≤ 1 * countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P :=
      mul_le_mul_of_nonneg_right he bot_le
    _ = _ := one_mul _

end WaveTurbulence.FinalCountG8.P101
