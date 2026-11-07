/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrT4
import Mathlib.Tactic

/-!
# Cross-side relations of the parent branches across a `true` operation at another member
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem sign_chLr {LG : LayeredGarden w} (s : LFSource p kind LG) (ε : Bool) :
    nodeSign (s.chosen ε).sig (chLr s ε).1 =
      (if ε then (-1 : ℤˣ) else 1) * nodeSign s.skeleton.sig s.placement.retained.1 := by
  cases ε
  · simp [chLr, chosenLeafEquiv]; rfl
  · have := coreLeafEquiv_sign s.skeleton s.placement s.placement.retained
    have hm : coreLeafMultiplier s.skeleton s.placement s.placement.retained = -1 := by
      simp [coreLeafMultiplier]
    rw [hm] at this
    exact this

/-- The two exceptional leaves of member `j` are unmoved (multiplier `1`) by a twist at `i`. -/
theorem cross_leaf_sign (con : LFConstruction P.srcI true) :
    nodeSign (P.srcJT con).skeleton.sig (P.srcJT con).placement.retained.1 =
      nodeSign P.srcJ.skeleton.sig P.srcJ.placement.retained.1 := by
  have h1 : (P.srcJT con).placement.retained =
      coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement j).retained :=
    CoreFamily.nextPlacement_retained A.family i j
  rw [h1]
  have := coreLeafEquiv_sign A.skeleton (A.family.placement i) (A.family.placement j).retained
  have hm : coreLeafMultiplier A.skeleton (A.family.placement i) (A.family.placement j).retained = 1 := by
    have D := A.family.pairData i j P.hij
    have hne := retained_ne_of_lower_ne A.skeleton (A.family.placement i) (A.family.placement j)
      (CoreFamily.lower_ne_of_ne A.family P.hij)
    have hne2 : (A.family.placement j).retained ≠ A.skeleton.pair (A.family.placement i).retained :=
      separated_retained_ne_pair A.skeleton (A.family.placement i) (A.family.placement j)
        D.blockLeft D.clLeft D.atLeft D.blockRight D.clRight D.atRight D.separated
    simp [coreLeafMultiplier, Ne.symm hne, hne2]
  rw [hm, one_mul] at this
  exact this

theorem cross_sign (con : LFConstruction P.srcI true) (ε : Bool) :
    nodeSign ((P.srcJT con).chosen ε).sig (chLr (P.srcJT con) ε).1 =
      nodeSign (P.srcJ.chosen ε).sig (chLr P.srcJ ε).1 := by
  rw [sign_chLr, sign_chLr, cross_leaf_sign P con]

theorem cross_lower (con : LFConstruction P.srcI true) :
    (P.srcJT con).placement.lower = coreBranchEquiv A.skeleton (A.family.placement i) P.srcJ.placement.lower :=
  CoreFamily.nextPlacement_lower A.family i j

theorem cross_CL (con : LFConstruction P.srcI true) :
    coreBranchEquiv A.skeleton (A.family.placement i)
      (GNode.parent P.srcJ.placement.lower.toNode P.srcJ.placement.nonroot) =
    GNode.parent (P.srcJT con).placement.lower.toNode (P.srcJT con).placement.nonroot := by
  have e : (coreBranchEquiv A.skeleton (A.family.placement i) P.srcJ.placement.lower).toNode =
      (P.srcJT con).placement.lower.toNode :=
    congrArg (fun b : GBranch _ => b.toNode) (cross_lower P con).symm
  exact (branchParent_transport A.skeleton (A.family.placement i) P.srcJ.placement.lower
    P.srcJ.placement.nonroot (CoreFamily.lower_ne_of_ne A.family P.hij.symm)).symm.trans
    (parent_congr e _ _)

theorem cross_CP (con : LFConstruction P.srcI true) :
    coreBranchEquiv A.skeleton (A.family.placement i)
      (GNode.parent (P.srcJ.skeleton.pair P.srcJ.placement.retained).toNode P.srcJ.placement.paired_nonroot) =
    GNode.parent ((P.srcJT con).skeleton.pair (P.srcJT con).placement.retained).toNode
      (P.srcJT con).placement.paired_nonroot := by
  have h1 : (P.srcJT con).placement.retained =
      coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement j).retained :=
    CoreFamily.nextPlacement_retained A.family i j
  have e : (coreLeafEquiv A.skeleton (A.family.placement i)
        (A.skeleton.pair (A.family.placement j).retained)).toNode =
      ((P.srcJT con).skeleton.pair (P.srcJT con).placement.retained).toNode := by
    rw [h1]
    exact (congrArg (fun l : GLeaf _ => l.toNode)
      (unitTwistGarden_pair A.skeleton (A.family.placement i) (A.family.placement j).retained)).symm
  have D := A.family.pairData i j P.hij
  exact (leafParent_transport A.skeleton (A.family.placement i) (A.skeleton.pair (A.family.placement j).retained)
    (A.family.placement j).paired_nonroot (Ne.symm D.paired_ne)).symm.trans (parent_congr e _ _)

theorem cross_cfFirst (con : LFConstruction P.srcI true) (ε : Bool) :
    cfFirst (P.srcJT con) ε = coreBranchEquiv A.skeleton (A.family.placement i) (cfFirst P.srcJ ε) := by
  classical
  unfold cfFirst
  rw [cross_sign P con ε]
  by_cases hs : nodeSign (P.srcJ.chosen ε).sig (chLr P.srcJ ε).1 = 1
  · rw [if_pos hs, if_pos hs]
    exact cross_lower P con
  · rw [if_neg hs, if_neg hs]
    cases ε
    · exact (cross_CP P con).symm
    · exact (cross_CL P con).symm

theorem cross_cfSecond (con : LFConstruction P.srcI true) (ε : Bool) :
    cfSecond (P.srcJT con) ε = coreBranchEquiv A.skeleton (A.family.placement i) (cfSecond P.srcJ ε) := by
  classical
  unfold cfSecond
  rw [cross_sign P con ε]
  by_cases hs : nodeSign (P.srcJ.chosen ε).sig (chLr P.srcJ ε).1 = 1
  · rw [if_pos hs, if_pos hs]
    cases ε
    · exact (cross_CP P con).symm
    · exact (cross_CL P con).symm
  · rw [if_neg hs, if_neg hs]
    exact cross_lower P con

theorem cross_cfLow (con : LFConstruction P.srcI true) (ε : Bool) :
    cfLow (P.srcJT con) ε = coreBranchEquiv A.skeleton (A.family.placement i) (cfLow P.srcJ ε) := by
  unfold cfLow
  cases ε
  · exact (cross_CL P con).symm
  · exact (cross_CP P con).symm

end WaveTurbulence.Stage1
