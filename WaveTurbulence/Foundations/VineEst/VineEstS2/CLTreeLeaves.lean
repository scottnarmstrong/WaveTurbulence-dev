/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLTreeLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPredecessorBudget

/-! # Every cropped leaf is an actual regional leaf or a fixed boundary value -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clTreeLeaf_nonroot (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (ℓ : GLeaf (CLTreeForest R)) : ℓ.1.2 ≠ [] := by
  intro hn
  have hp : 0 < (clRealizationTree R).order := by
    rw [clRealizationTree_order_eq_local_add_one hU R]
    omega
  have hl : [] ∈ (clRealizationTree R).leaves := by simpa only [hn] using ℓ.2
  cases ht : clRealizationTree R with
  | leaf => simp only [ht,TTree.order] at hp; omega
  | node l m r => simp only [ht,leaves,Finset.mem_union,nil_notMem_pre,false_or] at hl

theorem clTreeLeaf_mem_support (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (ℓ : GLeaf (CLTreeForest R)) : clTreeNode R ℓ.toNode ∈ clLocalSupport R := by
  have hn := clTreeLeaf_nonroot hU R ℓ
  let v := GNode.parent ℓ.toNode hn
  have he := Mole.parent_child_eq_node ℓ.toNode hn
  have hm := congrArg (clTreeNode R) he
  rw [clTreeNode_child] at hm
  rw [← hm]
  exact cl_child_mem_support hU R (clTreeBranch_mem hU R _) _

/-- Realization leaves remain actual source leaves; a new leaf created by
cutting a branch is necessarily one of the fixed four boundary labels. -/
theorem clTreeLeaf_source_or_boundary (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (ℓ : GLeaf (CLTreeForest R)) :
    (∃ l : GLeaf G.tree, clTreeNode R ℓ.toNode = l.toNode ∧ Mole.IsInternalLeaf G U l) ∨
      ∃ j : Fin 4, clTreeNode R ℓ.toNode = clBoundaryNodes R j := by
  classical
  have hs := clTreeLeaf_mem_support hU R ℓ
  rcases Finset.mem_union.mp hs with hr | hb
  · have hl : (clTreeNode R ℓ.toNode).1.2 ∈ (G.tree (clTreeNode R ℓ.toNode).1.1).leaves := by
      rcases (TTree.mem_nodes_iff _ _).mp (clTreeNode R ℓ.toNode).2 with hl | hv
      · exact hl
      · let v : GBranch G.tree := ⟨(clTreeNode R ℓ.toNode).1,hv⟩
        have hvU : v ∈ U := (branch_mem_clRealizationNodes v).mp hr
        obtain ⟨p,hp⟩ := clTreeBranch_surjective hU R v hvU
        let q : GBranch (CLTreeForest R) := ⟨(0,p.1),p.2⟩
        have he : clTreeNode R q.toNode = clTreeNode R ℓ.toNode :=
          (clTreeNode_branch R q).trans (congrArg GBranch.toNode hp)
        exact (Mole.branch_toNode_ne_leaf q ℓ (clTreeNode_injective R he)).elim
    let l : GLeaf G.tree := ⟨(clTreeNode R ℓ.toNode).1,hl⟩
    exact Or.inl ⟨l,rfl,(leaf_mem_clRealizationNodes l).mp hr⟩
  · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hb
    exact Or.inr ⟨j,hj.symm⟩

end WaveTurbulence.VineEstS2
