/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cls1
import Mathlib.Tactic

/-!
# The final data of a `false`-choice construction, explicitly; swapping the two members
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {ι : Type*}

theorem finalData_tree_false (s : LFSource p kind LG) (X : RegChain) (Q : RegCpl) (hX : X.wf = true)
    (hQ : Q.wf = true) (b : GBranch s.skeleton.tree) :
    (s.finalData false X Q hX hQ).tree b = if b = s.placement.lower then X else s.data.tree b := by
  by_cases hb : b = s.placement.lower
  · subst hb
    rw [if_pos rfl]
    exact Function.update_self _ _ _
  · rw [if_neg hb]
    exact (Function.update_of_ne hb _ _).trans (s.data.eraseTree_other _ _ hb)

theorem finalData_couple_false (s : LFSource p kind LG) (X : RegChain) (Q : RegCpl) (hX : X.wf = true)
    (hQ : Q.wf = true) (q : SourcePair s.skeleton) :
    (s.finalData false X Q hX hQ).couple q = if q = s.exceptional then Q else s.data.couple q := by
  by_cases hq : q = s.exceptional
  · subst hq
    rw [if_pos rfl]
    have : (s.finalData false X Q hX hQ).couple (s.pairs false s.exceptional) = Q := Function.update_self _ _ _
    rwa [LFSource.pairs_false] at this
  · rw [if_neg hq]
    have hne : s.pairs false q ≠ s.pairs false s.exceptional := fun he => hq ((s.pairs false).injective he)
    have e : (s.finalData false X Q hX hQ).couple (s.pairs false q) = s.data.couple q :=
      (Function.update_of_ne hne _ _).trans (s.base_couple_other false q hq)
    rwa [LFSource.pairs_false] at e

/-- The member context with the two members swapped. -/
@[expose] def PairCtx.swap {A : FamilyReconstruction w ι} {i j : ι} (P : PairCtx p kind A i j) :
    PairCtx p kind A j i where
  hij := P.hij.symm
  c := P.c
  el := P.elJ
  tc := P.tcJ
  cc := P.ccJ
  elJ := P.el
  tcJ := P.tc
  ccJ := P.cc

end WaveTurbulence.Stage1
