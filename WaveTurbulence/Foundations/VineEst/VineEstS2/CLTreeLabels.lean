/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLTreeBranchEquiv
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Subtrees

/-! # Actual node labels and conservation on the cut realization tree -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable abbrev CLTreeForest (R : CLRegionData G U a b) : Fin 1 → TTree := fun _ => clRealizationTree R

noncomputable def clTreeNode (R : CLRegionData G U a b) (x : GNode (CLTreeForest R)) : GNode G.tree :=
  ⟨(a.1.1,a.1.2++x.1.2),(Comb.subtree_nodes_iff (Comb.nodeSubtree_spec a.toNode) x.1.2).mp
    (cropTree_nodes_subset _ _ x.2)⟩

theorem clTreeNode_injective (R : CLRegionData G U a b) : Function.Injective (clTreeNode R) := by
  intro x y he
  have hp := congrArg (fun z : GNode G.tree => z.1.2) he
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) (List.append_cancel_left hp))

theorem clTreeNode_branch (R : CLRegionData G U a b) (v : GBranch (CLTreeForest R)) :
    clTreeNode R v.toNode = (clTreeBranch R ⟨v.1.2,v.2⟩).toNode := Subtype.ext rfl

theorem clTreeNode_child (R : CLRegionData G U a b) (v : GBranch (CLTreeForest R)) (i : Fin 3) :
    clTreeNode R (v.child i) = (clTreeBranch R ⟨v.1.2,v.2⟩).child i := by
  apply Subtype.ext
  exact Prod.ext rfl (List.append_assoc _ _ _).symm

theorem clTreeNode_sign (R : CLRegionData G U a b) (x : GNode (CLTreeForest R)) :
    G.sign (clTreeNode R x) = nodeSign (fun _ : Fin 1 => G.sign a.toNode) x.1 := by
  change pathSign (G.sig a.1.1) (a.1.2++x.1.2) = pathSign (pathSign (G.sig a.1.1) a.1.2) x.1.2
  exact Comb.pathSign_append _ _ _

end WaveTurbulence.VineEstS2
