/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreGraph
import Mathlib.Tactic

/-! # `BridgeSplitInput` (DH23 L1963): removing a bridge, counting the two sides separately

`𝔄(𝕄) ≤ 𝔄(𝕄[S]) · 𝔄(𝕄[S^c])` exactly (constants `K = 1`, `B = 0`) when `S` is attached by one bond and both sides
are connected. The label of the bridge is fixed by the conservation law on `S` (`OneExit.countEFree_le`); the circuit
ranks add (`F(𝕄) = F(𝕄[S]) = F(𝕄[S^c]) = 1`) and the cells split (`OneExit.ladderCells_eq_union`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem norm_split {L a b : ℝ} (hL : 0 < L) (hb : b ≠ 0) {χN χp χq : ℤ} (h : χN = χp + χq)
    (cN cp cq : ℝ) (hc : cN = cp * cq) :
    L ^ (-a * χN) * b ^ χN * cN =
      (L ^ (-a * χp) * b ^ χp * cp) * (L ^ (-a * χq) * b ^ χq * cq) := by
  subst h hc
  push_cast
  rw [mul_add, Real.rpow_add hL, zpow_add₀ hb]
  ring

variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem sameComponent_erase_congr (M : Molecule V D) {A B : Finset V} (h : A = B) (a b : V) :
    (Degen.eraseAtoms M A).SameComponent a b ↔ (Degen.eraseAtoms M B).SameComponent a b := by
  subst h; rfl

/-- `eraseAtoms` only depends on the erased set. -/
theorem afreeSup_erase_congr (M : Molecule V D) {A B : Finset V} (h : A = B) {d : ℕ} (L γ δ η C1 : ℝ) :
    AFreeSup (Degen.eraseAtoms M A) d L γ δ η C1 = AFreeSup (Degen.eraseAtoms M B) d L γ δ η C1 := by
  subst h; rfl


/-- **`BridgeSplitAt` with `K = 1`, `B = 0`.** -/
theorem bridgeSplitAt {d : ℕ} {L γ δ η C1 : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (hC : 0 < C1)
    (hlog : 0 < Real.log L ^ 2) :
    BridgeSplitAt.{u, v} d L γ δ η C1 1 0 := by
  intro V D _ _ _ M hcap hloop S hS hcross hconn hconnS hconnT P hP
  classical
  have hLp : 0 < L := by linarith
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcross
  let T : OneExit M := ⟨S, hS, x, hx⟩
  set Adm := lgAdm (d := d) M L γ η P with hAdm
  have hPpiece : ∀ S' ∈ MoleProp.ladderCells (piece M S), 0 ≤ P S' := fun S' hS' => by
    have := (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M
      ((isLadderCell_piece_iff S').mp this).1), ((isLadderCell_piece_iff S').mp this).1⟩)
  have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms M S), 0 ≤ P S' := fun S' hS' => by
    have := (MoleProp.isLadderCell_erase_iff M S S').mp (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M this.1), this.1⟩)
  have hcount := T.countEFree_le (d := d) (γ := γ) (δ := δ) hLp Adm
  have hmonoP : MoleProp.countEFree (piece M S) L γ δ (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility M (M.atoms \ S) Adm) ≤
      MoleProp.countEFree (piece M S) L γ δ (0 : Mom d) (lgAdm (piece M S) L γ η P) :=
    MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
      obtain ⟨κ0, ⟨hLG, hC'⟩, _, rfl⟩ := h
      exact ⟨MoleProp.largeGap_erase M L γ η 0 _ hLG, MoleProp.cellGapRestriction_erase M L 0 _ P _ hC'⟩
  have hmonoE : MoleProp.countEFree (Degen.eraseAtoms M S) L γ δ (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility M S Adm) ≤
      MoleProp.countEFree (Degen.eraseAtoms M S) L γ δ (0 : Mom d) (lgAdm (Degen.eraseAtoms M S) L γ η P) :=
    MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
      obtain ⟨κ0, ⟨hLG, hC'⟩, _, rfl⟩ := h
      exact ⟨MoleProp.largeGap_erase M L γ η 0 _ hLG, MoleProp.cellGapRestriction_erase M L 0 _ P _ hC'⟩
  -- components
  have hF1 : M.numComponents = 1 := Mole.numComponents_eq_one M
    ⟨M.atom x, M.atom_mem x⟩ hconn
  have hFp : (piece M S).numComponents = 1 := Mole.numComponents_eq_one (piece M S)
    (by rw [piece_atoms hS]; exact ⟨M.atom x, T.atom_x⟩) (by rw [piece_atoms hS]; exact hconnS)
  have hY : M.atoms \ (M.atoms \ S) = S := by rw [sdiff_sdiff_right_self, inf_eq_right.mpr hS]
  have hFe : (Degen.eraseAtoms M S).numComponents = 1 := by
    refine Mole.numComponents_eq_one (Degen.eraseAtoms M S) ⟨M.atom (M.mate x), ?_⟩ ?_
    · exact mem_sdiff.mpr ⟨M.atom_mem _, T.c_notMem⟩
    · intro a ha b hb
      have h1 := hconnT a ha b hb
      exact (sameComponent_erase_congr M hY a b).mp h1
  have hrank : M.circuitRank - (Degen.eraseAtoms M S).circuitRank - (piece M S).circuitRank =
      (M.numComponents : ℤ) - (Degen.eraseAtoms M S).numComponents - (piece M S).numComponents + 1 :=
    T.circuitRank_identity
  rw [hF1, hFp, hFe] at hrank
  have hrk : M.circuitRank = (piece M S).circuitRank + (Degen.eraseAtoms M S).circuitRank := by
    push_cast at hrank; omega
  have hcells := T.ladderCells_eq_union
  have hbne : (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ≠ 0 := by positivity
  have hnorm : MoleProp.freeNormalization M (d := d) L γ δ C1 P =
      MoleProp.freeNormalization (piece M S) (d := d) L γ δ C1 P *
        MoleProp.freeNormalization (Degen.eraseAtoms M S) (d := d) L γ δ C1 P := by
    unfold MoleProp.freeNormalization
    exact norm_split hLp hbne hrk _ _ _ (by rw [hcells])
  have np := MoleProp.freeNormalization_pos (piece M S) (d := d) (γ := γ) hLp hδ hC hlog P hPpiece
  have ne := MoleProp.freeNormalization_pos (Degen.eraseAtoms M S) (d := d) (γ := γ) hLp hδ hC hlog P hPerase
  have hmain : AFree M d L γ δ η C1 P ≤ AFree (piece M S) d L γ δ η C1 P *
      AFree (Degen.eraseAtoms M S) d L γ δ η C1 P := by
    unfold AFree
    rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization,
      MoleProp.countAFree_eq_normalization, hnorm, ENNReal.ofReal_mul np.le]
    calc _ ≤ ((MoleProp.countEFree (piece M S) L γ δ (0 : Mom d) (lgAdm (piece M S) L γ η P) *
            MoleProp.countEFree (Degen.eraseAtoms M S) L γ δ (0 : Mom d)
              (lgAdm (Degen.eraseAtoms M S) L γ η P) : ℕ∞) : ℝ≥0∞) *
          (ENNReal.ofReal (MoleProp.freeNormalization (piece M S) (d := d) L γ δ C1 P) *
            ENNReal.ofReal (MoleProp.freeNormalization (Degen.eraseAtoms M S) (d := d) L γ δ C1 P)) :=
          mul_le_mul' (ENat.toENNReal_mono (hcount.trans (mul_le_mul' hmonoP hmonoE))) le_rfl
      _ = _ := by rw [ENat.toENNReal_mul]; ring
  have h1 := afree_le_afreeSup (piece M S) (d := d) (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) P hPpiece
  have h2 := afree_le_afreeSup (Degen.eraseAtoms M S) (d := d) (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1)
    P hPerase
  have h4 : AFreeSup (Degen.eraseAtoms M S) d L γ δ η C1 = AFreeSup (piece M (M.atoms \ S)) d L γ δ η C1 :=
    afreeSup_erase_congr M (d := d) (A := S) (B := M.atoms \ (M.atoms \ S)) hY.symm L γ δ η C1
  rw [Real.rpow_zero, mul_one, ENNReal.ofReal_one, one_mul, ← h4]
  exact hmain.trans (mul_le_mul' h1 h2)

/-- **`BridgeSplitInput`** (DH23 L1963). -/
theorem bridgeSplitInput (d : ℕ) (γ η : ℝ) : BridgeSplitInput.{u, v} d γ η := by
  refine ⟨1, le_rfl, fun C1 hC1 δ hδ => ⟨1, 0, Real.exp 1, fun L hL => ?_⟩⟩
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hL
  have hl2 : 0 < Real.log L ^ 2 := by positivity
  exact @bridgeSplitAt.{u, v} d L γ δ η C1 hL1 hδ.1 (by linarith [hC1]) hl2

end WaveTurbulence.FinalCountG8
