/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.PartitionCoverBound
public import WaveTurbulence.Foundations.FinalCount.AppBLinkParents
import Mathlib.Tactic

/-! # The source ladder complexity is controlled by any actual ladder cover

Selected source ladders use the adopted F53 convention, including allowed
ambient end chords. This separately named quantity does not redefine the
older induced-ladder B2 rho.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def sourceFreeAtoms (M : Molecule V D) : Finset V :=
  M.atoms \ (Degen.sourceMaximalLadders M).biUnion id

noncomputable def sourceRho (M : Molecule V D) : ℕ :=
  (Degen.sourceMaximalLadders M).card+(sourceFreeAtoms M).card

theorem sourceLadderSet_nonempty (M : Molecule V D) {S : Finset V}
    (h : Degen.SourceLadderSet M S) : S.Nonempty := by
  obtain ⟨m,u,v,hL,rfl⟩ := h
  exact ⟨u 0,mem_union_left _ (mem_image.mpr ⟨0,mem_univ _,rfl⟩)⟩

theorem sourceRho_le_ladder_cover (M : Molecule V D) (hM : M.IsMolecule)
    (C : Finset (Finset V)) (hC : ∀ S ∈ C,Degen.SourceLadderSet M S) :
    sourceRho M ≤ C.card+(M.atoms \ C.biUnion id).card := by
  classical
  apply partition_cover_complexity_bound M.atoms (Degen.sourceMaximalLadders M) C
    (Degen.sourceMaximalLadders_pairwiseDisjoint M hM)
  · intro T hT
    exact Degen.sourceLadderSet_atoms_subset M (mem_filter.mp hT).2.1
  · intro T hT
    exact sourceLadderSet_nonempty M (mem_filter.mp hT).2.1
  · intro S hS
    exact sourceLadderSet_nonempty M (hC S hS)
  · intro S hS
    exact Degen.exists_sourceMaximalLadder_superset M (hC S hS)

end WaveTurbulence.Mole.AppbAlgorithm
