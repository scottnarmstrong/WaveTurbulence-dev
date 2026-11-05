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

theorem leavesBelowSet_inter_of_antichain {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (A B : Finset (GNode LG.garden.tree)) (hA : A ⊆ U) (hB : B ⊆ U) :
    LG.leavesBelowSet (A ∩ B) = LG.leavesBelowSet A ∩ LG.leavesBelowSet B := by
  classical
  ext ℓ
  constructor
  · intro h
    obtain ⟨u, hu, hd⟩ := Canon.Rel.mem_leavesBelowSet.mp h
    exact Finset.mem_inter.mpr
      ⟨Canon.Rel.mem_leavesBelowSet.mpr ⟨u, (Finset.mem_inter.mp hu).1, hd⟩,
        Canon.Rel.mem_leavesBelowSet.mpr ⟨u, (Finset.mem_inter.mp hu).2, hd⟩⟩
  · intro h
    obtain ⟨u, hu, hd⟩ := Canon.Rel.mem_leavesBelowSet.mp (Finset.mem_inter.mp h).1
    obtain ⟨v, hv, hd'⟩ := Canon.Rel.mem_leavesBelowSet.mp (Finset.mem_inter.mp h).2
    have he : u = v := by
      rcases Canon.isDesc_total hd hd' with huv | hvu
      · exact Canon.Rel.eq_of_isDesc_of_antichain hU (hA hu) (hB hv) huv
      · exact (Canon.Rel.eq_of_isDesc_of_antichain hU (hB hv) (hA hu) hvu).symm
    exact Canon.Rel.mem_leavesBelowSet.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, he.symm ▸ hv⟩, hd⟩

theorem leavesBelowSet_biUnion {w : ℕ} (LG : LayeredGarden w) (U : Finset (GNode LG.garden.tree)) :
    LG.leavesBelowSet U = U.biUnion GNode.leavesBelow := by
  classical
  ext ℓ
  simp only [Canon.Rel.mem_leavesBelowSet, Finset.mem_biUnion, GNode.leavesBelow,
    Finset.mem_filter, Finset.mem_univ, true_and]

end WaveTurbulence.Induct
