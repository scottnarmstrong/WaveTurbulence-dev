/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Canon.Decomp
/-! Boolean set operations for subtrees rooted in an antichain. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem completelyPaired_inter {w : ℕ} (G : Garden w) {S T : Finset (GLeaf G.tree)}
    (hS : G.CompletelyPaired S) (hT : G.CompletelyPaired T) : G.CompletelyPaired (S ∩ T) := by
  intro ℓ hℓ
  obtain ⟨hs, ht⟩ := Finset.mem_inter.mp hℓ
  exact ⟨(hS ℓ hs).1, Finset.mem_inter.mpr ⟨(hS ℓ hs).2, (hT ℓ ht).2⟩⟩

theorem leavesBelowSet_biUnion {w : ℕ} (LG : LayeredGarden w) (U : Finset (GNode LG.garden.tree)) :
    LG.leavesBelowSet U = U.biUnion GNode.leavesBelow := by
  classical
  ext ℓ
  simp only [Canon.Rel.mem_leavesBelowSet, Finset.mem_biUnion, GNode.leavesBelow,
    Finset.mem_filter, Finset.mem_univ, true_and]

end WaveTurbulence.Induct
