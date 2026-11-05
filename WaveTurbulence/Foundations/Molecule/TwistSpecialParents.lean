/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistExceptionalDarts

/-! # The two changed parent incidences of the unit twist

TARGET twistexplain (a): new u2 has the old parent of u0, and the moved
u0 leaf has the old parent of u2. The other parent identities are ordinary.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The new lower PC parent is the old paired-leaf parent. -/
theorem lower_new_parent :
    GNode.parent (coreBranchEquiv G P P.lower).toNode
      ((coreBranchEquiv_nonroot G P P.lower).mpr P.nonroot) =
      coreBranchEquiv G P (GNode.parent (G.pair P.retained).toNode P.paired_nonroot) := by
  apply parent_eq_of_child (i := (G.pair P.retained).1.2.getLast P.paired_nonroot)
  apply Subtype.ext
  change (coreBranchEquiv G P P.lower).1 =
    ((coreBranchEquiv G P (GNode.parent (G.pair P.retained).toNode P.paired_nonroot)).1.1,
      (coreBranchEquiv G P (GNode.parent (G.pair P.retained).toNode P.paired_nonroot)).1.2 ++ [_])
  rw [coreBranchEquiv_lower_val,coreBranchEquiv_fixed_val G P _ (paired_parent_outside G P)]
  have hh := congrArg (fun n : GNode G.tree => n.1)
    (Mole.parent_child_eq_node (G.pair P.retained).toNode P.paired_nonroot).symm
  simpa only [GLeaf.toNode,GBranch.child] using hh

/-- The new moved-u0 LP parent is the old lower-branch parent. -/
theorem paired_new_parent :
    GNode.parent (coreLeafEquiv G P (G.pair P.retained)).toNode
      ((coreLeafEquiv_nonroot G P (G.pair P.retained)).mpr P.paired_nonroot) =
      coreBranchEquiv G P (GNode.parent P.lower.toNode P.nonroot) := by
  apply parent_eq_of_child (i := P.lower.1.2.getLast P.nonroot)
  apply Subtype.ext
  change (coreLeafEquiv G P (G.pair P.retained)).1 =
    ((coreBranchEquiv G P (GNode.parent P.lower.toNode P.nonroot)).1.1,
      (coreBranchEquiv G P (GNode.parent P.lower.toNode P.nonroot)).1.2 ++ [_])
  rw [coreLeafEquiv_paired_val,coreBranchEquiv_fixed_val G P _ (lower_parent_outside G P)]
  have hh := congrArg (fun n : GNode G.tree => n.1)
    (Mole.parent_child_eq_node P.lower.toNode P.nonroot).symm
  simpa only [GBranch.toNode,GBranch.child] using hh

/-- The actual retained-leaf parent is exactly the lower branch. -/
theorem retained_parent : GNode.parent P.retained.toNode (retained_nonroot G P) = P.lower :=
  parent_eq_of_child _ P.child

end WaveTurbulence.Twist
