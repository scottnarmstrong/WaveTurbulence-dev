/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PinchBound
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2
import Mathlib.Tactic

/-! # The pinched-removal bound with constants (DH23 ylem2, (Y1) case 3) -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4

/-- **The pinched removal bound**: `𝔄(N) ≤ 𝔄(N ∖ Y)` (same LG parameter). -/
theorem pinch_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D),
      (∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) → ∀ T : Pinch N, (∀ v ∈ T.Y, N.deg v = 4) →
      (∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
        AFree N d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms N T.Y) d L γ δ η C1 P := by
  obtain ⟨Cstar, hCstar, h101⟩ := MoleProp.molecule_count_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := h101 (C1 / 2) (by linarith) δ hδ
  refine ⟨max R (Real.exp 1), fun L hL => ?_⟩
  intro V D _ _ _ N hcap T hdegY hconn P hP
  classical
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  unfold AFree
  -- loops
  by_cases hlo : ∃ z : D, N.atom z = N.atom (N.mate z)
  · obtain ⟨z, hz⟩ := hlo
    rw [MoleProp.countAFree_eq_zero_of_loop N hLp γ δ C1 η 0 _ (fun κ h => h.1) P z hz]
    exact bot_le
  have hloop : ∀ z, N.atom z ≠ N.atom (N.mate z) := fun z h => hlo ⟨z, h⟩
  -- the contracted molecule is bounded by Prop 10.1
  have hPa : ∀ S ∈ MoleProp.ladderCells T.aux, 0 ≤ Pinch.auxScale P S := by
    intro S hS
    obtain ⟨_, u, v, hL', rfl⟩ := mem_filter.mp hS
    obtain ⟨u', v', rfl, rfl, hY, hN⟩ := T.aux_sourceLadder_to hloop hL'
    unfold Pinch.auxScale
    rw [Pinch.ladderAtoms_comp_some, Pinch.preimage_image_some]
    exact hP _ (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N ⟨u', v', hN, rfl⟩),
      ⟨u', v', hN, rfl⟩⟩)
  have haux := hR L hLR T.aux (T.aux_isMolecule hcap hconn) (lgAdm T.aux L γ η (Pinch.auxScale P))
    (Pinch.auxScale P) (fun κ h => h.1) (fun κ h => h.2) hPa
  have hPpiece : ∀ S ∈ MoleProp.ladderCells (piece N T.Y), 0 ≤ P S := fun S hS => by
    have := (mem_filter.mp hS).2
    exact hP S (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N
      ((isLadderCell_piece_iff S).mp this).1), ((isLadderCell_piece_iff S).mp this).1⟩)
  have hPerase : ∀ S ∈ MoleProp.ladderCells (Degen.eraseAtoms N T.Y), 0 ≤ P S := fun S hS => by
    have := (MoleProp.isLadderCell_erase_iff N T.Y S).mp (mem_filter.mp hS).2
    exact hP S (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N this.1), this.1⟩)
  have hcount := T.countEFree_le hloop (d := d) (γ := γ) (η := η) hLp hδ.1 P
  have hmono : MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility N T.Y (lgAdm N L γ η P)) ≤
      MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d) (lgAdm (Degen.eraseAtoms N T.Y) L γ η P) :=
    MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
      obtain ⟨κ0, ⟨hLG, hC⟩, _, rfl⟩ := h
      exact ⟨MoleProp.largeGap_erase N L γ η 0 _ hLG, MoleProp.cellGapRestriction_erase N L 0 _ P _ hC⟩
  -- normalization
  have hrank := T.circuitRank_identity hconn
  have hFle := T.erase_numComponents_le
  have hra := T.aux_circuitRank hdegY hconn
  have na := MoleProp.freeNormalization_pos T.aux (d := d) (γ := γ) hLp hδ.1 (by linarith : (0 : ℝ) < C1 / 2)
    hlog0 (Pinch.auxScale P) hPa
  have ne := MoleProp.freeNormalization_pos (Degen.eraseAtoms N T.Y) (d := d) (γ := γ) hLp hδ.1
    (by linarith : (0 : ℝ) < C1) hlog0 P hPerase
  have hcells : MoleProp.cellProduct N L γ δ P ≤
      MoleProp.cellProduct T.aux L γ δ (Pinch.auxScale P) * MoleProp.cellProduct (Degen.eraseAtoms N T.Y) L γ δ P * 1 := by
    rw [cellProduct_split (fun S hS => T.cell_sub_or_disjoint hS) T.sub, mul_one]
    exact mul_le_mul_of_nonneg_right (T.cellProduct_piece_le hLp.le hδ.1.le hlog P hPa)
      (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPerase).le
  have hratio : MoleProp.freeNormalization N (d := d) L γ δ C1 P ≤
      MoleProp.freeNormalization T.aux (d := d) L γ δ (C1 / 2) (Pinch.auxScale P) *
        MoleProp.freeNormalization (Degen.eraseAtoms N T.Y) (d := d) L γ δ C1 P *
          ((1 / 2 : ℝ) ^ T.aux.circuitRank * 1) := by
    unfold MoleProp.freeNormalization
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact norm_ratio hL1 (by linarith [hγ.2]) hδ.1 hδ.2 (by linarith) (by linarith) (by omega)
      (by rw [hra]; positivity) (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 _ hPa).le
      (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPerase).le zero_le_one hcells
  have hfac : (T.Y.card : ℝ) * ((1 / 2 : ℝ) ^ T.aux.circuitRank * 1) ≤ 1 := by
    rw [hra, mul_one, zpow_add₀ (by norm_num), zpow_one, zpow_natCast]
    have h := sq_le_twentytwo_mul_two_pow T.Y.card
    have hle : (T.Y.card : ℝ) ≤ 2 ^ T.Y.card := by exact_mod_cast (Nat.lt_two_pow_self).le
    have h2 : (1 / 2 : ℝ) ^ T.Y.card * 2 ^ T.Y.card = 1 := by rw [← mul_pow]; norm_num
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) T.Y.card]
  rw [MoleProp.countAFree_eq_normalization]
  calc (MoleProp.countEFree N L γ δ (0 : Mom d) (lgAdm N L γ η P) : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization N (d := d) L γ δ C1 P)
      ≤ (((T.Y.card : ℕ∞) * MoleProp.countEFree T.aux L γ δ (0 : Mom d) (lgAdm T.aux L γ η (Pinch.auxScale P)) *
          MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d) (lgAdm (Degen.eraseAtoms N T.Y) L γ η P) :
            ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (MoleProp.freeNormalization T.aux (d := d) L γ δ (C1 / 2) (Pinch.auxScale P) *
            MoleProp.freeNormalization (Degen.eraseAtoms N T.Y) (d := d) L γ δ C1 P *
              ((1 / 2 : ℝ) ^ T.aux.circuitRank * 1)) :=
        mul_le_mul' (ENat.toENNReal_mono (hcount.trans (mul_le_mul' le_rfl hmono))) (ENNReal.ofReal_le_ofReal hratio)
    _ = MoleProp.countAFree T.aux L γ δ (C1 / 2) (0 : Mom d) (lgAdm T.aux L γ η (Pinch.auxScale P)) (Pinch.auxScale P) *
          MoleProp.countAFree (Degen.eraseAtoms N T.Y) L γ δ C1 (0 : Mom d) (lgAdm (Degen.eraseAtoms N T.Y) L γ η P) P *
            ENNReal.ofReal ((T.Y.card : ℝ) * ((1 / 2 : ℝ) ^ T.aux.circuitRank * 1)) := by
        rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization, ENat.toENNReal_mul,
          ENat.toENNReal_mul, ENat.toENNReal_coe, ENNReal.ofReal_mul (mul_nonneg na.le ne.le),
          ENNReal.ofReal_mul na.le, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        ring
    _ ≤ 1 * MoleProp.countAFree (Degen.eraseAtoms N T.Y) L γ δ C1 (0 : Mom d)
          (lgAdm (Degen.eraseAtoms N T.Y) L γ η P) P * 1 :=
        mul_le_mul' (mul_le_mul' haux le_rfl) (ENNReal.ofReal_le_one.mpr hfac)
    _ = _ := by ring

end WaveTurbulence.MoleProp4
