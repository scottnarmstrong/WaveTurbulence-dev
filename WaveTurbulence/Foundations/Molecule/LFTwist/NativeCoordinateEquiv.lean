/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ChoiceGeometry

/-! # Literal unchanged native branch coordinates for an LF construction -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed

@[expose] def pathSetEquiv {A B : Finset Path} (h : A = B) : ↥A ≃ ↥B where
  toFun q := ⟨q.1,h ▸ q.2⟩
  invFun q := ⟨q.1,h.symm ▸ q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def forestBranchEquiv {w : ℕ} {F H : Fin w → TTree} (h : F = H) : GBranch F ≃ GBranch H where
  toFun q := ⟨q.1,by rw [← h]; exact q.2⟩
  invFun q := ⟨q.1,by rw [h]; exact q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace LFConstruction
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
    (h : LFConstruction s ε)

@[expose] noncomputable def treeBranches (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower) :
    ChainBranchPath s.data b ≃ ChainBranchPath h.data (s.branches ε b) :=
  pathSetEquiv (by rw [h.tree_other b hb,s.ordinary_branch_sign ε b hb])

@[expose] noncomputable def coupleBranches (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional) :
    GBranch (decodedCouple (s.data.couple q)).tree ≃ GBranch (decodedCouple (h.data.couple (s.pairs ε q))).tree :=
  forestBranchEquiv (congrArg (fun Q => (decodedCouple Q).tree) (h.couple_other q hq).symm)

theorem ordinary_tree_branch_layer (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower)
    (c : ChainBranchPath s.data b) :
    layerAt LG (chainContextBranch s.data s.plain b c).1 =
      layerAt h.output (chainContextBranch h.data (s.chosen_plain ε) (s.branches ε b) (h.treeBranches b hb c)).1 :=
  h.ordinaryTreeLayers b hb c.1 (TTree.branching_subset_nodes _ c.2)

theorem ordinary_couple_branch_layer (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional)
    (c : GBranch (decodedCouple (s.data.couple q)).tree) :
    layerAt LG (coupleContextBranch s.data s.plain q c).1 =
      layerAt h.output (coupleContextBranch h.data (s.chosen_plain ε) (s.pairs ε q) (h.coupleBranches q hq c)).1 := by
  rw [coupleContextBranch_address,coupleContextBranch_address]
  exact h.ordinaryCoupleLayers q hq c.1.1 c.1.2 (TTree.branching_subset_nodes _ c.2)

/-- All ordinary couple endpoints preserve their original tree index. -/
theorem ordinary_couple_root_index (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional) (i : Fin 2) :
    (coupleRoot h.data (s.chosen_plain ε) (s.pairs ε q) i).1 =
      (coupleRoot s.data s.plain q i).1 := by
  have hs := s.ordinary_pair_sides ε q hq
  fin_cases i
  · change (inflatedPosition (s.chosen ε) h.data.tree ((s.pairs ε q).firstLeaf (s.chosen_plain ε)).toNode).1 =
      (inflatedPosition s.skeleton s.data.tree (q.firstLeaf s.plain).toNode).1
    exact (inflatedPosition_index (s.chosen ε) h.data.tree _).trans
      ((congrArg (fun l : GLeaf (s.chosen ε).tree => l.1.1) hs.1).trans
        ((s.leaves_index ε (q.firstLeaf s.plain)).trans
          (inflatedPosition_index s.skeleton s.data.tree (q.firstLeaf s.plain).toNode).symm))
  · change (inflatedPosition (s.chosen ε) h.data.tree ((s.pairs ε q).secondLeaf (s.chosen_plain ε)).toNode).1 =
      (inflatedPosition s.skeleton s.data.tree (q.secondLeaf s.plain).toNode).1
    exact (inflatedPosition_index (s.chosen ε) h.data.tree _).trans
      ((congrArg (fun l : GLeaf (s.chosen ε).tree => l.1.1) hs.2).trans
        ((s.leaves_index ε (q.secondLeaf s.plain)).trans
          (inflatedPosition_index s.skeleton s.data.tree (q.secondLeaf s.plain).toNode).symm))

end LFConstruction
end WaveTurbulence.LFTwist
