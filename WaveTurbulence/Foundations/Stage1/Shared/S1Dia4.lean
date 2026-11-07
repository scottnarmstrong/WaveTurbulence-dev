/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrT8
import Mathlib.Tactic

/-!
# Final data of a `true`-choice construction, explicitly
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

theorem finalData_tree_true (s : LFSource p kind LG) (X : RegChain) (Q : RegCpl) (hX : X.wf = true)
    (hQ : Q.wf = true) (b : GBranch s.skeleton.tree) :
    (s.finalData true X Q hX hQ).tree (s.branches true b) =
      if b = s.placement.lower then X else s.data.tree b := by
  by_cases hb : b = s.placement.lower
  · subst hb
    rw [if_pos rfl]
    exact Function.update_self _ _ _
  · rw [if_neg hb]
    have hne : s.branches true b ≠ s.branches true s.placement.lower := fun he => hb ((s.branches true).injective he)
    exact (Function.update_of_ne hne _ _).trans (s.base_tree_other true b hb)

theorem finalData_couple_true (s : LFSource p kind LG) (X : RegChain) (Q : RegCpl) (hX : X.wf = true)
    (hQ : Q.wf = true) (q : SourcePair s.skeleton) :
    (s.finalData true X Q hX hQ).couple (s.pairs true q) =
      if q = s.exceptional then Q else s.data.couple q := by
  by_cases hq : q = s.exceptional
  · subst hq
    rw [if_pos rfl]
    exact Function.update_self _ _ _
  · rw [if_neg hq]
    have hne : s.pairs true q ≠ s.pairs true s.exceptional := fun he => hq ((s.pairs true).injective he)
    exact (Function.update_of_ne hne _ _).trans (s.base_couple_other true q hq)

end WaveTurbulence.Stage1
