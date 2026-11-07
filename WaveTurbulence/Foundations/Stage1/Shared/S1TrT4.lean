/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrT3
import Mathlib.Tactic

/-!
# Closed forms of the parent branches of the exceptional leaves of the chosen skeleton
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

theorem pairs_exc_eq (ε : Bool) : s.pairs ε s.exceptional =
    pairOfLeaf (s.chosen ε) (s.chosen_plain ε) (chLr s ε) :=
  sourcePairEquiv_pairOfLeaf s.plain (s.chosen_plain ε) (chosenLeafEquiv s.skeleton s.placement ε)
    (chosenLeafEquiv_pair s.skeleton s.placement ε) s.placement.retained

theorem exc_pos (ε : Bool) (hs : nodeSign (s.chosen ε).sig (chLr s ε).1 = 1) :
    (s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε) = chLr s ε ∧
    (s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε) = (s.chosen ε).pair (chLr s ε) := by
  rw [pairs_exc_eq]
  exact pairOfLeaf_sides_pos _ (s.chosen_plain ε) _ hs

theorem exc_neg (ε : Bool) (hs : ¬ nodeSign (s.chosen ε).sig (chLr s ε).1 = 1) :
    (s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε) = (s.chosen ε).pair (chLr s ε) ∧
    (s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε) = chLr s ε := by
  rw [pairs_exc_eq]
  exact pairOfLeaf_sides_neg _ (s.chosen_plain ε) _ hs

/-- The original branch whose core layer is the parent layer of the first exceptional leaf. -/
@[expose] noncomputable def cfFirst (ε : Bool) : GBranch s.skeleton.tree := by
  classical
  exact if nodeSign (s.chosen ε).sig (chLr s ε).1 = 1 then s.placement.lower
    else (if ε then GNode.parent s.placement.lower.toNode s.placement.nonroot
      else GNode.parent (s.skeleton.pair s.placement.retained).toNode s.placement.paired_nonroot)

@[expose] noncomputable def cfSecond (ε : Bool) : GBranch s.skeleton.tree := by
  classical
  exact if nodeSign (s.chosen ε).sig (chLr s ε).1 = 1 then
      (if ε then GNode.parent s.placement.lower.toNode s.placement.nonroot
      else GNode.parent (s.skeleton.pair s.placement.retained).toNode s.placement.paired_nonroot)
    else s.placement.lower

@[expose] noncomputable def cfLow (ε : Bool) : GBranch s.skeleton.tree :=
  if ε then GNode.parent (s.skeleton.pair s.placement.retained).toNode s.placement.paired_nonroot
  else GNode.parent s.placement.lower.toNode s.placement.nonroot

theorem parent_Lp (ε : Bool) (h : ((s.chosen ε).pair (chLr s ε)).toNode.1.2 ≠ []) :
    (s.branches ε).symm (GNode.parent ((s.chosen ε).pair (chLr s ε)).toNode h) =
      if ε then GNode.parent s.placement.lower.toNode s.placement.nonroot
      else GNode.parent (s.skeleton.pair s.placement.retained).toNode s.placement.paired_nonroot := by
  cases ε
  · exact parent_Lp_false s h
  · exact parent_Lp_true s h

theorem parent_first (ε : Bool) (h : ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode.1.2 ≠ []) :
    (s.branches ε).symm (GNode.parent ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode h) =
      cfFirst s ε := by
  classical
  unfold cfFirst
  by_cases hs : nodeSign (s.chosen ε).sig (chLr s ε).1 = 1
  · rw [if_pos hs]
    have e := (exc_pos s ε hs).1
    rw [parent_congr (congrArg (fun l : GLeaf (s.chosen ε).tree => l.toNode) e) h
      (by have := exc_first_nonroot s ε; rw [e] at this; exact this.1)]
    exact parent_Lr s ε _
  · rw [if_neg hs]
    have e := (exc_neg s ε hs).1
    rw [parent_congr (congrArg (fun l : GLeaf (s.chosen ε).tree => l.toNode) e) h
      (by have := exc_first_nonroot s ε; rw [e] at this; exact this.1)]
    exact parent_Lp s ε _

theorem parent_second (ε : Bool) (h : ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode.1.2 ≠ []) :
    (s.branches ε).symm (GNode.parent ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode h) =
      cfSecond s ε := by
  classical
  unfold cfSecond
  by_cases hs : nodeSign (s.chosen ε).sig (chLr s ε).1 = 1
  · rw [if_pos hs]
    have e := (exc_pos s ε hs).2
    rw [parent_congr (congrArg (fun l : GLeaf (s.chosen ε).tree => l.toNode) e) h
      (by have := exc_first_nonroot s ε; rw [e] at this; exact this.2)]
    exact parent_Lp s ε _
  · rw [if_neg hs]
    have e := (exc_neg s ε hs).2
    rw [parent_congr (congrArg (fun l : GLeaf (s.chosen ε).tree => l.toNode) e) h
      (by have := exc_first_nonroot s ε; rw [e] at this; exact this.2)]
    exact parent_Lr s ε _

theorem parent_low (ε : Bool) (h : (s.branches ε s.placement.lower).toNode.1.2 ≠ []) :
    (s.branches ε).symm (GNode.parent (s.branches ε s.placement.lower).toNode h) = cfLow s ε := by
  cases ε
  · exact parent_low_false s h
  · exact parent_low_true s h

end WaveTurbulence.Stage1
