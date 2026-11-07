/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.BetaCutCount
import Mathlib.Tactic

/-! # Circuit ranks and cells for a set attached by two bonds at one atom

`χ(N) = χ(N[Y ∪ {w}]) + χ(N ∖ Y)` when all three molecules are connected, and the ladder cells of `N` are those
of `N[Y ∪ {w}]` (inside `Y`) and those of `N ∖ Y` (disjoint from `Y`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Cut2
variable {N : Molecule V D} (T : Cut2 N)

theorem card_darts' (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) :
    Fintype.card D = Fintype.card (Degen.RetainedDart N (N.atoms \ insert T.w T.Y)) +
      Fintype.card (Degen.RetainedDart N T.Y) := by
  classical
  have hc : Fintype.card (MoleProp.DeletedDart N T.Y) + Fintype.card (Degen.RetainedDart N T.Y) =
      Fintype.card D := by
    rw [Fintype.card_subtype, Fintype.card_subtype, add_comm, card_filter_add_card_filter_not, card_univ]
  rw [← hc]
  congr 1
  have hback : ∀ p : Degen.RetainedDart N (N.atoms \ insert T.w T.Y),
      ¬(N.atom p.val ∉ T.Y ∧ N.atom (N.mate p.val) ∉ T.Y) := by
    intro p
    have hp := p.property
    simp only [mem_sdiff, not_and, not_not] at hp
    have h1 : N.atom p.val ∈ insert T.w T.Y := hp.1 (N.atom_mem _)
    have h2 : N.atom (N.mate p.val) ∈ insert T.w T.Y := hp.2 (N.atom_mem _)
    rintro ⟨h3, h4⟩
    rcases mem_insert.mp h1 with h1 | h1
    · rcases mem_insert.mp h2 with h2 | h2
      · exact hloop p.val (h1.trans h2.symm)
      · exact h4 h2
    · exact h3 h1
  exact Fintype.card_congr
    { toFun := fun z => pieceDart' N (insert T.w T.Y) z.val (deleted_in_piece T.sub T.w_notMem T.hX z)
      invFun := fun p => ⟨p.val, hback p⟩
      left_inv := fun z => rfl
      right_inv := fun p => rfl }

variable (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z))
include hloop

theorem bonds_eq : N.bonds.card = (piece N (insert T.w T.Y)).bonds.card + (Degen.eraseAtoms N T.Y).bonds.card := by
  have h1 := Mole.two_mul_card_bonds N
  have h2 := Mole.two_mul_card_bonds (piece N (insert T.w T.Y))
  have h3 := Mole.two_mul_card_bonds (Degen.eraseAtoms N T.Y)
  have h4 := T.card_darts' hloop
  omega

theorem circuitRank_eq (hF : N.numComponents = 1) (hF1 : (piece N (insert T.w T.Y)).numComponents = 1)
    (hF2 : (Degen.eraseAtoms N T.Y).numComponents = 1) :
    N.circuitRank = (piece N (insert T.w T.Y)).circuitRank + (Degen.eraseAtoms N T.Y).circuitRank := by
  classical
  have hW : insert T.w T.Y ⊆ N.atoms := insert_subset (N.atom_mem (N.mate T.x)) T.sub
  have hat : N.atoms.card = T.Y.card + (N.atoms \ T.Y).card := by
    rw [card_sdiff_of_subset T.sub]; have := card_le_card T.sub; omega
  have hwc : (insert T.w T.Y).card = T.Y.card + 1 := card_insert_of_notMem T.w_notMem
  unfold Molecule.circuitRank
  rw [T.bonds_eq hloop, hF, hF1, hF2, hat, piece_atoms hW, hwc]
  change _ = _ + (((Degen.eraseAtoms N T.Y).bonds.card : ℤ) - ((N.atoms \ T.Y).card : ℤ) + _)
  push_cast
  ring

omit hloop in
theorem isLadderCell_card {S : Finset V} (hS : MoleProp.IsLadderCell N S) : S.card = 4 := by
  obtain ⟨u, v, h, rfl⟩ := hS
  exact Degen.ladderAtoms_card_of_injective h.2.1

theorem cells_piece_eq : MoleProp.ladderCells (piece N (insert T.w T.Y)) =
    (MoleProp.ladderCells N).filter (fun S => S ⊆ T.Y) := by
  classical
  have hW : insert T.w T.Y ⊆ N.atoms := insert_subset (N.atom_mem (N.mate T.x)) T.sub
  ext S
  simp only [MoleProp.ladderCells, mem_filter, mem_powerset, isLadderCell_piece_iff, piece_atoms hW]
  constructor
  · rintro ⟨hSW, hc, hsub⟩
    refine ⟨⟨hSW.trans hW, hc⟩, ?_⟩
    rcases T.cell_sub_or_disjoint hc with h | h
    · exact h
    · exfalso
      have : S ⊆ {T.w} := by
        intro z hz
        rcases mem_insert.mp (hsub hz) with h' | h'
        · exact mem_singleton.mpr h'
        · exact absurd h' (disjoint_left.mp h hz)
      have := card_le_card this
      rw [isLadderCell_card hc, card_singleton] at this
      omega
  · rintro ⟨⟨hSA, hc⟩, hsub⟩
    exact ⟨hsub.trans (subset_insert _ _), hc, hsub.trans (subset_insert _ _)⟩

end Cut2

end WaveTurbulence.FinalCountG8
