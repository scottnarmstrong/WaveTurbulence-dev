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

/-- Restriction consumes the original source conservation equations; none is
assumed for an invented tree or for artificial boundary labels. -/
theorem clTreeNode_conservation {E : Type*} [AddCommGroup E] (R : CLRegionData G U a b)
    (κ : GNode G.tree → E)
    (hκ : ∀ v : GBranch G.tree, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (v : GBranch (CLTreeForest R)) :
    κ (clTreeNode R v.toNode) = κ (clTreeNode R (v.child 0))-
      κ (clTreeNode R (v.child 1))+κ (clTreeNode R (v.child 2)) := by
  rw [clTreeNode_branch,clTreeNode_child,clTreeNode_child,clTreeNode_child]
  exact hκ _

/-- The signed sum rule on the actual cropped tree, including its physical
boundary leaves. This is the garden predecessor calculation's leaf expansion. -/
theorem clTreeNode_sum_rule {E : Type*} [AddCommGroup E] (R : CLRegionData G U a b)
    (κ : GNode G.tree → E)
    (hκ : ∀ v : GBranch G.tree, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (x : GNode (CLTreeForest R)) :
    ((G.sign (clTreeNode R x) : ℤˣ) : ℤ) • κ (clTreeNode R x) =
      ∑ ℓ ∈ x.leavesBelow, ((G.sign (clTreeNode R ℓ.toNode) : ℤˣ) : ℤ) • κ (clTreeNode R ℓ.toNode) := by
  simp_rw [clTreeNode_sign]
  exact WaveTurbulence.sum_rule (tree := CLTreeForest R)
    (fun _ : Fin 1 => G.sign a.toNode) (fun x => κ (clTreeNode R x))
    (clTreeNode_conservation R κ hκ) x

end WaveTurbulence.VineEstS2
