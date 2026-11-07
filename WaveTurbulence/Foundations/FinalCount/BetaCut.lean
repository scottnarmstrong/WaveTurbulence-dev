/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.BetaCutRank
public import WaveTurbulence.Foundations.FinalCount.BridgeSplit
import Mathlib.Tactic

/-! # `BetaCutInput` (DH23 L1784, used at L1963)

For a set `S` attached by two bonds at the cut atom `w`:
`𝔄(𝕄) ≤ |S| · 𝔄(𝕄[S ∪ {w}]) · 𝔄(𝕄[S^c])` (constants `K = 1`, `B = 0`; `|S| ≤ |𝕄| + 1`), with no restriction on the
directions of the two bonds. See `Cut2.countEFree_le`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

section Cells
variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable {N : Molecule V D} (T : Cut2 N)

theorem Cut2.cellProduct_eq (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (L γ δ : ℝ) (P : Finset V → ℝ) :
    MoleProp.cellProduct N L γ δ P =
      MoleProp.cellProduct (piece N (insert T.w T.Y)) L γ δ P *
        MoleProp.cellProduct (Degen.eraseAtoms N T.Y) L γ δ P := by
  classical
  unfold MoleProp.cellProduct
  rw [← prod_filter_mul_prod_filter_not (MoleProp.ladderCells N) (fun S => S ⊆ T.Y)]
  have h1 := T.cells_piece_eq hloop
  have h2 : MoleProp.ladderCells (Degen.eraseAtoms N T.Y) =
      (MoleProp.ladderCells N).filter (fun S => ¬ S ⊆ T.Y) := by
    ext S
    simp only [MoleProp.ladderCells, mem_filter, mem_powerset, MoleProp.isLadderCell_erase_iff]
    constructor
    · rintro ⟨hSA, hc, hdis⟩
      refine ⟨⟨hSA.trans sdiff_subset, hc⟩, fun hsub => ?_⟩
      obtain ⟨u, v, _, rfl⟩ := hc
      have hmem : u 0 ∈ Molecule.ladderAtoms u v := mem_union_left _ (mem_image_of_mem _ (mem_univ 0))
      exact disjoint_left.mp hdis hmem (hsub hmem)
    · rintro ⟨⟨hSA, hc⟩, hnsub⟩
      have hdis := (T.cell_sub_or_disjoint hc).resolve_left hnsub
      refine ⟨fun a ha => mem_sdiff.mpr ⟨hSA ha, disjoint_left.mp hdis ha⟩, hc, hdis⟩
  rw [h1, h2]

end Cells

/-- **`BetaCutAt` with `K = 1`, `B = 0`.** -/
theorem betaCutAt {d : ℕ} {L γ δ η C1 : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (hC : 0 < C1)
    (hlog : 0 < Real.log L ^ 2) :
    BetaCutAt.{u, v} d L γ δ η C1 1 0 := by
  intro V D _ _ _ M hcap hloop w S hw hS hwS hcross hto hconn hconn1 hconn2 P hP
  classical
  have hLp : 0 < L := by linarith
  obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.mp hcross
  have hsame : M.atom (M.mate x) = M.atom (M.mate y) := by
    rw [hto x (by rw [hxyeq]; simp), hto y (by rw [hxyeq]; simp)]
  let T : Cut2 M := ⟨S, hS, x, y, hxyeq, hxy, hsame⟩
  have hTw : T.w = w := hto x (by rw [hxyeq]; simp)
  have hW : insert w S ⊆ M.atoms := insert_subset hw hS
  set Adm := lgAdm (d := d) M L γ η P with hAdm
  have hPpiece : ∀ S' ∈ MoleProp.ladderCells (piece M (insert w S)), 0 ≤ P S' := fun S' hS' => by
    have := (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M
      ((isLadderCell_piece_iff S').mp this).1), ((isLadderCell_piece_iff S').mp this).1⟩)
  have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms M S), 0 ≤ P S' := fun S' hS' => by
    have := (MoleProp.isLadderCell_erase_iff M S S').mp (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M this.1), this.1⟩)
  have hcount := T.countEFree_le hloop (d := d) (γ := γ) (δ := δ) (η := η) hLp hδ P
  rw [hTw] at hcount
  have hmonoE : MoleProp.countEFree (Degen.eraseAtoms M S) L γ δ (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility M S Adm) ≤
      MoleProp.countEFree (Degen.eraseAtoms M S) L γ δ (0 : Mom d) (lgAdm (Degen.eraseAtoms M S) L γ η P) :=
    MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
      obtain ⟨κ0, ⟨hLG, hC'⟩, _, rfl⟩ := h
      exact ⟨MoleProp.largeGap_erase M L γ η 0 _ hLG, MoleProp.cellGapRestriction_erase M L 0 _ P _ hC'⟩
  -- components
  have hF1 : M.numComponents = 1 := Mole.numComponents_eq_one M ⟨w, hw⟩ hconn
  have hFp : (piece M (insert w S)).numComponents = 1 := Mole.numComponents_eq_one (piece M (insert w S))
    (by rw [piece_atoms hW]; exact ⟨w, mem_insert_self _ _⟩) (by rw [piece_atoms hW]; exact hconn1)
  have hY : M.atoms \ (M.atoms \ S) = S := by rw [sdiff_sdiff_right_self, inf_eq_right.mpr hS]
  have hFe : (Degen.eraseAtoms M S).numComponents = 1 := by
    refine Mole.numComponents_eq_one (Degen.eraseAtoms M S) ⟨w, ?_⟩ ?_
    · exact mem_sdiff.mpr ⟨hw, hwS⟩
    · intro a ha b hb
      have h1 := hconn2 a ha b hb
      exact (sameComponent_erase_congr M hY a b).mp h1
  have hrk : M.circuitRank = (piece M (insert w S)).circuitRank + (Degen.eraseAtoms M S).circuitRank := by
    have := T.circuitRank_eq hloop hF1 (by rw [hTw]; exact hFp) hFe
    rw [hTw] at this; exact this
  have hcells : MoleProp.cellProduct M = fun L γ δ P => MoleProp.cellProduct (piece M (insert w S)) L γ δ P *
        MoleProp.cellProduct (Degen.eraseAtoms M S) L γ δ P := by
    funext L γ δ P
    have := T.cellProduct_eq hloop L γ δ P
    rw [hTw] at this; exact this
  have hbne : (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ≠ 0 := by positivity
  have hnorm : MoleProp.freeNormalization M (d := d) L γ δ C1 P =
      MoleProp.freeNormalization (piece M (insert w S)) (d := d) L γ δ C1 P *
        MoleProp.freeNormalization (Degen.eraseAtoms M S) (d := d) L γ δ C1 P := by
    unfold MoleProp.freeNormalization
    exact norm_split hLp hbne hrk _ _ _ (by rw [hcells])
  have np := MoleProp.freeNormalization_pos (piece M (insert w S)) (d := d) (γ := γ) hLp hδ hC hlog P hPpiece
  have ne := MoleProp.freeNormalization_pos (Degen.eraseAtoms M S) (d := d) (γ := γ) hLp hδ hC hlog P hPerase
  have hmain : AFree M d L γ δ η C1 P ≤ (S.card : ℝ≥0∞) * (AFree (piece M (insert w S)) d L γ δ η C1 P *
      AFree (Degen.eraseAtoms M S) d L γ δ η C1 P) := by
    unfold AFree
    rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization,
      MoleProp.countAFree_eq_normalization, hnorm, ENNReal.ofReal_mul np.le]
    calc _ ≤ (((S.card : ℕ∞) * MoleProp.countEFree (piece M (insert w S)) L γ δ (0 : Mom d)
              (lgAdm (piece M (insert w S)) L γ η P) *
            MoleProp.countEFree (Degen.eraseAtoms M S) L γ δ (0 : Mom d)
              (lgAdm (Degen.eraseAtoms M S) L γ η P) : ℕ∞) : ℝ≥0∞) *
          (ENNReal.ofReal (MoleProp.freeNormalization (piece M (insert w S)) (d := d) L γ δ C1 P) *
            ENNReal.ofReal (MoleProp.freeNormalization (Degen.eraseAtoms M S) (d := d) L γ δ C1 P)) :=
          mul_le_mul' (ENat.toENNReal_mono (hcount.trans (mul_le_mul' le_rfl hmonoE))) le_rfl
      _ = _ := by rw [ENat.toENNReal_mul, ENat.toENNReal_mul, ENat.toENNReal_coe]; ring
  have h1 := afree_le_afreeSup (piece M (insert w S)) (d := d) (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1)
    P hPpiece
  have h2 := afree_le_afreeSup (Degen.eraseAtoms M S) (d := d) (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1)
    P hPerase
  have h4 : AFreeSup (Degen.eraseAtoms M S) d L γ δ η C1 = AFreeSup (piece M (M.atoms \ S)) d L γ δ η C1 :=
    afreeSup_erase_congr M (d := d) (A := S) (B := M.atoms \ (M.atoms \ S)) hY.symm L γ δ η C1
  have hcard : (S.card : ℝ≥0∞) ≤ ENNReal.ofReal (1 * Real.log L ^ (0 : ℝ) * (M.atoms.card + 1)) := by
    rw [Real.rpow_zero, mul_one, one_mul, ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    exact le_add_right (by exact_mod_cast card_le_card hS)
  rw [← h4]
  calc AFree M d L γ δ η C1 P ≤ _ := hmain
    _ ≤ ENNReal.ofReal (1 * Real.log L ^ (0 : ℝ) * (M.atoms.card + 1)) *
        (AFreeSup (piece M (insert w S)) d L γ δ η C1 * AFreeSup (Degen.eraseAtoms M S) d L γ δ η C1) :=
        mul_le_mul' hcard (mul_le_mul' h1 h2)
    _ = _ := by ring

/-- **`BetaCutInput`** (DH23 L1784, L1963). -/
theorem betaCutInput (d : ℕ) (γ η : ℝ) : BetaCutInput.{u, v} d γ η := by
  refine ⟨1, le_rfl, fun C1 hC1 δ hδ => ⟨1, 0, Real.exp 1, fun L hL => ?_⟩⟩
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hL
  have hl2 : 0 < Real.log L ^ 2 := by positivity
  exact @betaCutAt.{u, v} d L γ δ η C1 hL1 hδ.1 (by linarith [hC1]) hl2

end WaveTurbulence.FinalCountG8
