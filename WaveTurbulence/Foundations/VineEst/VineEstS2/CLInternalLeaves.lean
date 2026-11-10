/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLTreeLeaves

/-! # Every actual internal paired leaf occurs in the cropped realization -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clInternalLeaf_surjective (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (ℓ : GLeaf G.tree) (hℓ : Mole.IsInternalLeaf G U ℓ) :
    ∃ l : GLeaf (CLTreeForest R), clTreeNode R l.toNode = ℓ.toNode := by
  obtain ⟨hm,hn,hpn,hg⟩ := hℓ
  have hp : GNode.parent ℓ.toNode hn ∈ U := hg.1
  obtain ⟨p,hp'⟩ := clTreeBranch_surjective hU R _ hp
  let q : GBranch (CLTreeForest R) := ⟨(0,p.1),p.2⟩
  let i := ℓ.1.2.getLast hn
  let x := q.child i
  have he : clTreeNode R x = ℓ.toNode :=
    (clTreeNode_child R q i).trans ((congrArg (fun v : GBranch G.tree => v.child i) hp').trans
      (Mole.parent_child_eq_node ℓ.toNode hn))
  rcases (TTree.mem_nodes_iff _ _).mp x.2 with hl | hb
  · exact ⟨⟨x.1,hl⟩,he⟩
  · let z : GBranch (CLTreeForest R) := ⟨x.1,hb⟩
    have hz : (clTreeBranch R ⟨z.1.2,z.2⟩).toNode = ℓ.toNode :=
      (clTreeNode_branch R z).symm.trans he
    exact (Mole.branch_toNode_ne_leaf _ ℓ hz).elim

end WaveTurbulence.VineEstS2
