/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Geo2

/-! # ZP-SURJ: parents in the unit-twisted skeleton -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Mole

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

theorem parent_of_addr {S : Garden w} {n : GNode S.tree} (hn : n.1.2 ≠ []) {c : GBranch S.tree}
    (hc : c.1 = (n.1.1, n.1.2.dropLast)) : n.parent hn = c := Subtype.ext hc.symm

theorem twist_parent_lower (hn' : (coreBranchEquiv G P P.lower).toNode.1.2 ≠ []) :
    GNode.parent (coreBranchEquiv G P P.lower).toNode hn' =
      coreBranchEquiv G P (GNode.parent (G.pair P.retained).toNode P.paired_nonroot) := by
  have h1 := coreBranchEquiv_lower_val G P
  have h2 := coreBranchEquiv_fixed_val G P (GNode.parent (G.pair P.retained).toNode P.paired_nonroot)
    (paired_parent_outside G P)
  refine parent_of_addr (S := unitTwistGarden G P) hn' ?_
  rw [h2]
  show _ = (((coreBranchEquiv G P P.lower).1.1, (coreBranchEquiv G P P.lower).1.2.dropLast))
  rw [h1]
  rfl

theorem twist_parent_paired
    (hn' : ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)).toNode.1.2 ≠ []) :
    GNode.parent ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)).toNode hn' =
      coreBranchEquiv G P (GNode.parent P.lower.toNode P.nonroot) := by
  have h0 : (unitTwistGarden G P).pair (coreLeafEquiv G P P.retained) = coreLeafEquiv G P (G.pair P.retained) :=
    unitTwistGarden_pair G P P.retained
  have h1 : ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)).1 = P.lower.1 := by
    rw [h0]; exact coreLeafEquiv_paired_val G P
  have h2 := coreBranchEquiv_fixed_val G P (GNode.parent P.lower.toNode P.nonroot) (lower_parent_outside G P)
  refine parent_of_addr (S := unitTwistGarden G P) hn' ?_
  rw [h2]
  show _ = ((((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)).1.1,
    (((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)).1.2.dropLast)))
  rw [h1]
  rfl

end WaveTurbulence.ZpSurj
