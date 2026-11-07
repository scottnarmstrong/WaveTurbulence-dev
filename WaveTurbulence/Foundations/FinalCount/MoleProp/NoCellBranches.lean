/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneCircuitNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ZeroLossDeletion
import Mathlib.Tactic

/-! # Neutral atom deletion away from every ladder cell

DH23 10.1 uses this extension when splitting an operation(b) that affects
no ladder into two atom removals. Actual cell avoidance is graph branch data;
all numerical local counting and deviations remain proved internally.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem ladderCells_erase_eq_of_all_avoid (M : Molecule V D) (v : V)
    (hcell : ∀ S ∈ ladderCells M, v ∉ S) :
    ladderCells (Degen.eraseAtoms M {v}) = ladderCells M := by
  classical
  rw [ladderCells_erase_eq_filter]
  apply filter_eq_self.mpr
  intro S hS
  exact disjoint_singleton_right.mpr (hcell S hS)

/-- No conditional local count or ladder comparison remains in this
source operation bound. The constant C1 is chosen after the uniform local C. -/
theorem countAFree_erase_three_two_circuits_of_no_cell (d : ℕ) (hdim : 3 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cstar L₀ : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ L ≥ L₀, 1 ≤ Real.log L →
    ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D], ∀ (M : Molecule V D), M.IsMolecule →
    ∀ v ∈ M.atoms, M.deg v = 3 →
    (∀ S ∈ ladderCells M, v ∉ S) →
    (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank-2 →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P := by
  classical
  obtain ⟨C,R,hC,hBound⟩ := degree_three_deletion_bound d hdim γ hγ
  refine ⟨C+1,max R 1,by linarith only [hC],?_⟩
  intro C1 hC1 L hL hlog δ hδ V' D' _ _ _ M hM v hv hdeg hcell hχ Adm P hP
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hC1p : 0 < C1 := by linarith only [hC,hC1]
  have ha : 0 ≤ (d : ℝ)-γ := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hdim
    linarith only [hdR,hγ.2]
  have hlog0 : 0 < Real.log L ^ 2 := by have hh : 0 < Real.log L := zero_lt_one.trans_le hlog; positivity
  have hcells := ladderCells_erase_eq_of_all_avoid M v hcell
  have hprod : cellProduct M L γ δ P = cellProduct (Degen.eraseAtoms M {v}) L γ δ P := by
    unfold cellProduct
    rw [hcells]
  have hPpost : ∀ S ∈ ladderCells (Degen.eraseAtoms M {v}), 0 ≤ P S := by rw [hcells]; exact hP
  have hpost := freeNormalization_pos (Degen.eraseAtoms M {v}) (d := d) (γ := γ) hL0 hδ.1 hC1p hlog0 P hPpost
  have hc := hBound L ((le_max_left R 1).trans hL) δ hδ M hM v hv hdeg Adm
  have hh := countAFree_le_ratio_of_countEFree_le M (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d)
    Adm (erasedFreeAdmissibility M {v} Adm) P P _ hc
    (freeNormalization_pos M (d := d) (γ := γ) hL0 hδ.1 hC1p hlog0 P hP).le hpost
  have hj : M.circuitRank-(Degen.eraseAtoms M {v}).circuitRank = 2 := by omega
  have hr := freeNormalization_ratio_of_product_eq M (Degen.eraseAtoms M {v}) (d := d) (γ := γ)
    hL0 hδ.1 hC1p P hprod (cellProduct_pos (Degen.eraseAtoms M {v}) (γ := γ) hL0.le hδ.1.le hlog0 P hPpost)
  rw [hj] at hr
  norm_num only [Int.cast_ofNat,zpow_ofNat] at hr
  have hlarge : C+1 ≤ C1^2 := by nlinarith only [hC,hC1]
  have hs := triple_deletion_scalar_le_one hL1 ha hδ hC1p hC hlarge
  have hs' : (⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))⌉₊ : ℝ) * freeNormalization M (d := d) L γ δ C1 P /
      freeNormalization (Degen.eraseAtoms M {v}) (d := d) L γ δ C1 P ≤ 1 := by
    rw [mul_div_assoc,hr]
    rw [show -((d : ℝ)-γ)*2 = -2*((d : ℝ)-γ) by ring]
    simpa only [mul_assoc] using hs
  have he : ENNReal.ofReal ((⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))⌉₊ : ℝ) * freeNormalization M (d := d) L γ δ C1 P /
      freeNormalization (Degen.eraseAtoms M {v}) (d := d) L γ δ C1 P) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs'
  apply hh.trans
  calc
    _ ≤ 1 * countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P :=
      mul_le_mul_of_nonneg_right he bot_le
    _ = _ := one_mul _


theorem countAFree_erase_one_circuit_of_no_cell (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2)
    (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L → ∀ C1 ≥ (1 : ℝ),
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ v ∈ M.atoms,
    (M.deg v = 2 ∨ (M.deg v = 3 ∧ (Degen.newComponents M {v}).card = 2)) →
    (∀ S ∈ ladderCells M, v ∉ S) →
    (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank-1 →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P := by
  classical
  obtain ⟨C,R,hC,hBound⟩ := one_loss_deletion_bound d hd γ hγ η hη hηmax
  refine ⟨max (max R 1) (((C+1)*δ⁻¹)^(η⁻¹)),?_⟩
  intro L hL hlog C1 hC1 V D _ _ _ M hM v hv hbranch hcell hχ Adm P hAdm hP
  have hLR : R ≤ L := (le_max_left R 1).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right R 1).trans ((le_max_left _ _).trans hL)
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hC1p : 0 < C1 := zero_lt_one.trans_le hC1
  have hlog0 : 0 < Real.log L ^ 2 := by have hh : 0 < Real.log L := zero_lt_one.trans_le hlog; positivity
  have hdeg : M.deg v ≤ 3 := by rcases hbranch with h2 | ⟨h3,_⟩ <;> omega
  have hcells := ladderCells_erase_eq_of_all_avoid M v hcell
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


end WaveTurbulence.MoleProp
