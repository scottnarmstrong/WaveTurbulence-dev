/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrT2
import Mathlib.Tactic

/-!
# Parents of the exceptional leaves and of the lower joint under a unit twist
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

theorem retained_ne_pair : P.retained ≠ G.pair P.retained := fun he =>
  Garden.pair_ne_of_unmarked P.unmarked he.symm

theorem tw_parent_ret (h : (coreLeafEquiv G P P.retained).toNode.1.2 ≠ []) :
    (coreBranchEquiv G P).symm (GNode.parent (coreLeafEquiv G P P.retained).toNode h) = P.lower := by
  rw [Equiv.symm_apply_eq]
  have := leafParent_transport G P P.retained (retained_nonroot G P) (retained_ne_pair P)
  rw [this, retained_parent]

theorem tw_parent_pair (h : (coreLeafEquiv G P (G.pair P.retained)).toNode.1.2 ≠ []) :
    (coreBranchEquiv G P).symm (GNode.parent (coreLeafEquiv G P (G.pair P.retained)).toNode h) =
      GNode.parent P.lower.toNode P.nonroot := by
  rw [Equiv.symm_apply_eq]
  exact paired_new_parent G P

theorem tw_parent_lower (h : (coreBranchEquiv G P P.lower).toNode.1.2 ≠ []) :
    (coreBranchEquiv G P).symm (GNode.parent (coreBranchEquiv G P P.lower).toNode h) =
      GNode.parent (G.pair P.retained).toNode P.paired_nonroot := by
  rw [Equiv.symm_apply_eq]
  exact lower_new_parent G P

theorem parent_congr {tree : Fin w → TTree} {n1 n2 : GNode tree} (e : n1 = n2) (h1 : n1.1.2 ≠ [])
    (h2 : n2.1.2 ≠ []) : GNode.parent n1 h1 = GNode.parent n2 h2 := by subst e; rfl

variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- The retained leaf of the chosen skeleton. -/
@[expose] noncomputable def chLr (ε : Bool) : GLeaf (s.chosen ε).tree :=
  chosenLeafEquiv s.skeleton s.placement ε s.placement.retained

theorem chLp_eq (ε : Bool) : (s.chosen ε).pair (chLr s ε) =
    chosenLeafEquiv s.skeleton s.placement ε (s.skeleton.pair s.placement.retained) :=
  (chosenLeafEquiv_pair s.skeleton s.placement ε _).symm

theorem parent_Lr (ε : Bool) (h : (chLr s ε).toNode.1.2 ≠ []) :
    (s.branches ε).symm (GNode.parent (chLr s ε).toNode h) = s.placement.lower := by
  cases ε
  · exact retained_parent s.skeleton s.placement
  · exact tw_parent_ret s.placement _

theorem parent_Lp_false (h : ((s.chosen false).pair (chLr s false)).toNode.1.2 ≠ []) :
    (s.branches false).symm (GNode.parent ((s.chosen false).pair (chLr s false)).toNode h) =
      GNode.parent (s.skeleton.pair s.placement.retained).toNode s.placement.paired_nonroot := rfl

theorem parent_Lp_true (h : ((s.chosen true).pair (chLr s true)).toNode.1.2 ≠ []) :
    (s.branches true).symm (GNode.parent ((s.chosen true).pair (chLr s true)).toNode h) =
      GNode.parent s.placement.lower.toNode s.placement.nonroot := by
  have e : ((s.chosen true).pair (chLr s true)).toNode =
      (coreLeafEquiv s.skeleton s.placement (s.skeleton.pair s.placement.retained)).toNode :=
    congrArg (fun l : GLeaf (s.chosen true).tree => l.toNode) (chLp_eq s true)
  rw [parent_congr e h ((coreLeafEquiv_nonroot s.skeleton s.placement _).mpr s.placement.paired_nonroot)]
  exact tw_parent_pair s.placement _

theorem parent_low_false (h : (s.branches false s.placement.lower).toNode.1.2 ≠ []) :
    (s.branches false).symm (GNode.parent (s.branches false s.placement.lower).toNode h) =
      GNode.parent s.placement.lower.toNode s.placement.nonroot := rfl

theorem parent_low_true (h : (s.branches true s.placement.lower).toNode.1.2 ≠ []) :
    (s.branches true).symm (GNode.parent (s.branches true s.placement.lower).toNode h) =
      GNode.parent (s.skeleton.pair s.placement.retained).toNode s.placement.paired_nonroot :=
  tw_parent_lower s.placement _

end WaveTurbulence.Stage1
