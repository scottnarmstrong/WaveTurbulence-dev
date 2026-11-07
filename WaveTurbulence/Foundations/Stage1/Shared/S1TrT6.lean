/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrT5
import Mathlib.Tactic

/-!
# The glue specification across a `true`-choice operation at another member
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem nodeSign_branches_lower {LG : LayeredGarden w} (s : LFSource p kind LG) (ε : Bool) :
    nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1 =
      (if ε then (-1 : ℤˣ) else 1) * nodeSign s.skeleton.sig s.placement.lower.1 := by
  cases ε
  · simp; rfl
  · have := coreBranchEquiv_sign s.skeleton s.placement s.placement.lower
    rw [if_pos rfl] at this
    have e : (-1 : ℤˣ) * nodeSign s.skeleton.sig s.placement.lower.1 = -nodeSign s.skeleton.sig s.placement.lower.1 :=
      neg_one_mul _
    change nodeSign (unitTwistGarden s.skeleton s.placement).sig
      (coreBranchEquiv s.skeleton s.placement s.placement.lower).1 = (-1 : ℤˣ) * _
    rw [e]
    exact this

theorem cross_zeta (con : LFConstruction P.srcI true) (ε : Bool) :
    nodeSign ((P.srcJT con).chosen ε).sig ((P.srcJT con).branches ε (P.srcJT con).placement.lower).1 =
      nodeSign (P.srcJ.chosen ε).sig (P.srcJ.branches ε P.srcJ.placement.lower).1 := by
  rw [nodeSign_branches_lower, nodeSign_branches_lower]
  congr 1
  rw [cross_lower P con]
  have hs := coreBranchEquiv_sign A.skeleton (A.family.placement i) P.srcJ.placement.lower
  have hb' : P.srcJ.placement.lower ≠ (A.family.placement i).lower :=
    CoreFamily.lower_ne_of_ne A.family P.hij.symm
  have hs' : nodeSign (unitTwistGarden A.skeleton (A.family.placement i)).sig
      (coreBranchEquiv A.skeleton (A.family.placement i) P.srcJ.placement.lower).1 =
      nodeSign A.skeleton.sig P.srcJ.placement.lower.1 := by
    split_ifs at hs with hc
    · exact absurd hc hb'
    · exact hs
  exact hs'

end WaveTurbulence.Stage1
