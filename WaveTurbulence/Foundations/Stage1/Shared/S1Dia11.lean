/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia10
import Mathlib.Tactic

/-!
# Diamond for two `true` operations: final data and states
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem doubleBranch_commute_addr (hij : i ≠ j) (b : GBranch A.skeleton.tree) :
    (A.family.doubleBranch i j b).1 = (A.family.doubleBranch j i b).1 :=
  (A.family.doubleBranch_pair hij b).trans (((A.family.pairData i j hij).branch_commute b).symm.trans
    (A.family.doubleBranch_pair hij.symm b).symm)

theorem doubleLeaf_commute_addr (hij : i ≠ j) (l : GLeaf A.skeleton.tree) :
    (A.family.doubleLeaf i j l).1 = (A.family.doubleLeaf j i l).1 :=
  (A.family.doubleLeaf_pair hij l).trans (((A.family.pairData i j hij).leaf_commute l).symm.trans
    (A.family.doubleLeaf_pair hij.symm l).symm)

theorem PairCtx.TT_FD_tree (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (b : GBranch A.skeleton.tree) :
    (P.specT con hj).FD.tree ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b)) =
      if b = (A.family.placement j).lower then hj.newTree
      else if b = (A.family.placement i).lower then con.newTree else A.data.tree b := by
  have e1 := finalData_tree_true (P.srcJT con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf
    (coreBranchEquiv A.skeleton (A.family.placement i) b)
  have e3 : (P.srcJT con).data.tree (coreBranchEquiv A.skeleton (A.family.placement i) b) =
      if b = (A.family.placement i).lower then con.newTree else A.data.tree b :=
    finalData_tree_true P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf b
  have hl := cross_lower P con
  refine e1.trans ?_
  rw [e3]
  have hcond : (coreBranchEquiv A.skeleton (A.family.placement i) b = (P.srcJT con).placement.lower) ↔
      b = (A.family.placement j).lower := by
    rw [hl]; exact (coreBranchEquiv A.skeleton (A.family.placement i)).injective.eq_iff
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem PairCtx.TT_FD_couple (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (q : SourcePair A.skeleton) :
    (P.specT con hj).FD.couple ((P.srcJT con).pairs true (P.srcI.pairs true q)) =
      if q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained then hj.newCouple
      else if q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained then con.newCouple
      else A.data.couple q := by
  have e1 := finalData_couple_true (P.srcJT con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf
    (P.srcI.pairs true q)
  have e3 : (P.srcJT con).data.couple (P.srcI.pairs true q) =
      if q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained then con.newCouple
        else A.data.couple q :=
    finalData_couple_true P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf q
  have hex := P.exc_cross con
  refine e1.trans ?_
  rw [e3]
  have hcond : (P.srcI.pairs true q = (P.srcJT con).exceptional) ↔
      q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained := by
    rw [hex]; exact (P.srcI.pairs true).injective.eq_iff
  split_ifs <;> first | rfl | (exfalso; tauto)

end WaveTurbulence.Stage1
