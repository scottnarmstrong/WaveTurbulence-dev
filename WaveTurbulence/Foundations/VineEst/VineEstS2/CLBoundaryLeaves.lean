/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryNodes

/-! # The three actual boundary leaves of the cropped realization -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clOutBoundaryNode (R : CLRegionData G U a b) (j : Fin 3) : GNode G.tree :=
  clBoundaryNodes R j.succ

theorem clOutBoundary_not_realization (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (j : Fin 3) : ¬ Mole.InIncidenceRealization G U (clOutBoundaryNode R j) := by
  intro hj
  have hr := (cl_realization_iff hU R _).mp hj
  have hi : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact hr.2.1 (GNode.isDesc_refl _)
  · exact hr.2.2.1 (GNode.isDesc_refl _)
  · exact hr.2.2.2 (GNode.isDesc_refl _)

theorem clChildNode_surjective (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : GBranch G.tree) (hv : v ∈ U) (i : Fin 3) :
    ∃ x : GNode (CLTreeForest R), clTreeNode R x = v.child i := by
  obtain ⟨p,hp⟩ := clTreeBranch_surjective hU R v hv
  let q : GBranch (CLTreeForest R) := ⟨(0,p.1),p.2⟩
  exact ⟨q.child i,(clTreeNode_child R q i).trans (congrArg (fun v : GBranch G.tree => v.child i) hp)⟩

theorem clOutBoundary_exists_node (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (j : Fin 3) : ∃ x : GNode (CLTreeForest R), clTreeNode R x = clOutBoundaryNode R j := by
  have hd := hU
  have hi : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact clChildNode_surjective hU R a hd.2.1 R.excluded
  · exact clChildNode_surjective hU R b hd.2.2.1 R.positive
  · exact clChildNode_surjective hU R b hd.2.2.1 R.negative

theorem clOutBoundary_exists_leaf (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (j : Fin 3) : ∃ l : GLeaf (CLTreeForest R), clTreeNode R l.toNode = clOutBoundaryNode R j := by
  obtain ⟨x,hx⟩ := clOutBoundary_exists_node hU R j
  rcases (TTree.mem_nodes_iff _ _).mp x.2 with hl | hb
  · exact ⟨⟨x.1,hl⟩,hx⟩
  · let v : GBranch (CLTreeForest R) := ⟨x.1,hb⟩
    have hm := (clTreeNode_branch R v).symm.trans hx
    have hr := (Mole.branch_incidence_realization_iff G U _).mpr (clTreeBranch_mem hU R ⟨v.1.2,v.2⟩)
    exact (clOutBoundary_not_realization hU R j (hm ▸ hr)).elim

noncomputable def clBoundaryLeaf (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (j : Fin 3) : GLeaf (CLTreeForest R) := Classical.choose (clOutBoundary_exists_leaf hU R j)

theorem clBoundaryLeaf_node (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (j : Fin 3) :
    clTreeNode R (clBoundaryLeaf hU R j).toNode = clOutBoundaryNode R j :=
  Classical.choose_spec (clOutBoundary_exists_leaf hU R j)

theorem clBoundaryLeaf_injective (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    Function.Injective (clBoundaryLeaf hU R) := by
  intro i j he
  have hm := congrArg (fun l : GLeaf (CLTreeForest R) => clTreeNode R l.toNode) he
  have hn := (clBoundaryLeaf_node hU R i).symm.trans (hm.trans (clBoundaryLeaf_node hU R j))
  exact Fin.succ_inj.mp (clBoundaryNodes_injective hU R hn)

end WaveTurbulence.VineEstS2
