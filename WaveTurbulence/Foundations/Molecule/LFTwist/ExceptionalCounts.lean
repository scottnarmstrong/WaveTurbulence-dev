/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.OrdinaryCounts

/-! # Both exceptional contributions are concentrated in one original tree -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed

private theorem pairOfLeaf_indices {w : ℕ} (G : Garden w) (hG : G.IsPlain) (l : GLeaf G.tree)
    (j : Fin w) (hl : l.1.1 = j) (hp : (G.pair l).1.1 = j) :
    ((pairOfLeaf G hG l).firstLeaf hG).1.1 = j ∧ ((pairOfLeaf G hG l).secondLeaf hG).1.1 = j := by
  by_cases hs : nodeSign G.sig l.1 = 1
  · have he := pairOfLeaf_sides_pos G hG l hs
    exact ⟨(congrArg (fun z : GLeaf G.tree => z.1.1) he.1).trans hl,
      (congrArg (fun z : GLeaf G.tree => z.1.1) he.2).trans hp⟩
  · have he := pairOfLeaf_sides_neg G hG l hs
    exact ⟨(congrArg (fun z : GLeaf G.tree => z.1.1) he.1).trans hp,
      (congrArg (fun z : GLeaf G.tree => z.1.1) he.2).trans hl⟩

namespace LFSource
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

theorem exceptional_indices : (s.exceptional.firstLeaf s.plain).1.1 = s.placement.lower.1.1 ∧
    (s.exceptional.secondLeaf s.plain).1.1 = s.placement.lower.1.1 :=
  pairOfLeaf_indices s.skeleton s.plain s.placement.retained s.placement.lower.1.1
    (congrArg (fun n : GNode s.skeleton.tree => n.1.1) s.placement.child) s.placement_tree_index.symm

theorem chosen_exceptional_indices (ε : Bool) :
    ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).1.1 = s.placement.lower.1.1 ∧
    ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).1.1 = s.placement.lower.1.1 := by
  have he : s.pairs ε s.exceptional =
      pairOfLeaf (s.chosen ε) (s.chosen_plain ε) (chosenLeafEquiv s.skeleton s.placement ε s.placement.retained) :=
    sourcePairEquiv_pairOfLeaf s.plain (s.chosen_plain ε) (chosenLeafEquiv s.skeleton s.placement ε)
      (chosenLeafEquiv_pair s.skeleton s.placement ε) s.placement.retained
  rw [he]
  apply pairOfLeaf_indices
  · exact (s.leaves_index ε s.placement.retained).trans
      (congrArg (fun n : GNode s.skeleton.tree => n.1.1) s.placement.child)
  · exact (congrArg (fun z : GLeaf (s.chosen ε).tree => z.1.1)
      (chosenLeafEquiv_pair s.skeleton s.placement ε s.placement.retained).symm).trans
        ((s.leaves_index ε (s.skeleton.pair s.placement.retained)).trans s.placement_tree_index.symm)

end LFSource

private theorem rawTreeTopCount_concentrated {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (p : ℕ) (b : GBranch S.tree) (j : Fin w) :
    rawTreeTopCount LG D hS p b j = if b.1.1 = j then rawTreeLayerCount LG D hS p b else 0 := by
  classical
  unfold rawTreeTopCount rawTreeLayerCount
  simp only [chainContextBranch_index D hS]
  by_cases hj : b.1.1 = j
  · simp only [hj,ite_true,true_and]
  · simp only [hj,ite_false,false_and,Finset.sum_const_zero]

private theorem rawCoupleTopCount_concentrated {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (p : ℕ) (q : SourcePair S) (j₀ j : Fin w)
    (hf : (q.firstLeaf hS).1.1 = j₀) (hs : (q.secondLeaf hS).1.1 = j₀) :
    rawCoupleTopCount LG D hS p q j = if j₀ = j then rawCoupleLayerCount LG D hS p q else 0 := by
  classical
  unfold rawCoupleTopCount rawCoupleLayerCount
  simp only [coupleContextBranch_index D hS q j₀ hf hs]
  by_cases hj : j₀ = j
  · simp only [hj,ite_true,true_and]
  · simp only [hj,ite_false,false_and,Finset.sum_const_zero]

namespace LFConstruction
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
    (h : LFConstruction s ε)

/-- The source scalar combined layer-p count preserves the exceptional
contribution to each tree, using the actual CL same-tree geometry. -/
theorem exceptional_topCounts_eq (j : Fin w) :
    rawTreeTopCount LG s.data s.plain p s.placement.lower j +
      rawCoupleTopCount LG s.data s.plain p s.exceptional j =
    rawTreeTopCount h.output h.data (s.chosen_plain ε) p (s.branches ε s.placement.lower) j +
      rawCoupleTopCount h.output h.data (s.chosen_plain ε) p (s.pairs ε s.exceptional) j := by
  rw [rawTreeTopCount_concentrated,rawTreeTopCount_concentrated,
    rawCoupleTopCount_concentrated _ _ _ _ _ _ _ s.exceptional_indices.1 s.exceptional_indices.2,
    rawCoupleTopCount_concentrated _ _ _ _ _ _ _ (s.chosen_exceptional_indices ε).1 (s.chosen_exceptional_indices ε).2,
    s.branches_index ε s.placement.lower]
  by_cases hj : s.placement.lower.1.1 = j
  · simp only [hj,ite_true]
    exact h.combinedTopCount
  · simp only [hj,ite_false,Nat.zero_add]

end LFConstruction
end WaveTurbulence.LFTwist
