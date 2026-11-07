/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia13
public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia8
import Mathlib.Tactic

/-!
# Diamond for two `true` operations: the final layered gardens agree (core and trees)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.TT_pos (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (b : GBranch A.skeleton.tree) (q : Path) :
    addrExt (inflatedPosition (P.opJT con hj).output.skeleton (P.opJT con hj).output.data.tree
      ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b)).toNode) q =
    addrExt (inflatedPosition (P.swap.opJT hj con).output.skeleton (P.swap.opJT hj con).output.data.tree
      ((P.swap.srcJT hj).branches true (coreBranchEquiv A.skeleton (A.family.placement j) b)).toNode) q :=
  congrArg (fun x => addrExt x q) (infl_cast (P.TT_skel con hj) _ _ (P.TT_data_heq con hj) _ _
    (doubleBranch_commute_addr (A := A) P.hij b))

theorem PairCtx.TT_core (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (b : GBranch A.skeleton.tree) :
    layerAt (P.constT con hj).output ((P.opJT con hj).output.data.corePosition
      ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b))) =
    layerAt (P.swap.constT hj con).output ((P.opJT con hj).output.data.corePosition
      ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b))) := by
  have a1 := P.T_core con hj b
  have a2 := P.swap.T_core hj con b
  have hpos := corePosition_cast (P.TT_skel con hj) _ _ (P.TT_data_heq con hj)
    ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b))
    ((P.swap.srcJT hj).branches true (coreBranchEquiv A.skeleton (A.family.placement j) b))
    (doubleBranch_commute_addr (A := A) P.hij b)
  exact a1.trans (a2.symm.trans (congrArg (layerAt (P.swap.constT hj con).output) hpos.symm))

theorem nodeSign_twist_lower {G : Garden w} (Pl : CorePlacement G) :
    nodeSign (unitTwistGarden G Pl).sig (coreBranchEquiv G Pl Pl.lower).1 = -nodeSign G.sig Pl.lower.1 := by
  have hs := coreBranchEquiv_sign G Pl Pl.lower
  rw [if_pos rfl] at hs
  exact hs

theorem nodeSign_cast {S S' : Garden w} (hs : S = S') (a a' : Address w) (h : a = a') :
    nodeSign S.sig a = nodeSign S'.sig a' := by subst hs; subst h; rfl

theorem PairCtx.TT_tree (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (b : GBranch A.skeleton.tree) (q : Path)
    (hq : q ∈ (((P.opJT con hj).output.data.tree
      ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b))).plug
      (nodeSign (P.opJT con hj).output.skeleton.sig
        ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b)).1) .leaf).branching) :
    layerAt (P.constT con hj).output (addrExt (inflatedPosition (P.opJT con hj).output.skeleton
      (P.opJT con hj).output.data.tree
      ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b)).toNode) q) =
    layerAt (P.swap.constT hj con).output (addrExt (inflatedPosition (P.opJT con hj).output.skeleton
      (P.opJT con hj).output.data.tree
      ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b)).toNode) q) := by
  have hcg := congrArg (layerAt (P.swap.constT hj con).output) (P.TT_pos con hj b q).symm
  have hT := P.TT_FD_tree con hj b
  have hl := cross_lower P con
  by_cases hbj : b = (A.family.placement j).lower
  · subst hbj
    have hT' : (P.opJT con hj).output.data.tree
        ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement j).lower)) =
        hj.newTree := by
      refine hT.trans ?_
      rw [if_pos rfl]
    have hne : (A.family.placement j).lower ≠ (A.family.placement i).lower :=
      CoreFamily.lower_ne_of_ne A.family P.hij.symm
    -- signs
    have hs1 : nodeSign (P.opJT con hj).output.skeleton.sig ((P.srcJT con).branches true
        (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement j).lower)).1 =
        -nodeSign A.skeleton.sig (A.family.placement j).lower.1 := by
      have e1 : (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement j).lower) =
          (A.family.nextPlacement i j).lower := (CoreFamily.nextPlacement_lower A.family i j).symm
      have a1 := nodeSign_twist_lower (A.family.nextPlacement i j)
      rw [← e1] at a1
      exact a1.trans (congrArg Neg.neg (nodeSign_twist_other (A.family.placement i) _ hne))
    have hs2 : nodeSign (P.swap.opJT hj con).output.skeleton.sig ((P.swap.srcJT hj).branches true
        (coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement j).lower)).1 =
        -nodeSign A.skeleton.sig (A.family.placement j).lower.1 := by
      have a1 := nodeSign_twist_other (A.family.nextPlacement j i)
        (coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement j).lower) (by
          rw [CoreFamily.nextPlacement_lower]
          exact fun he => hne ((coreBranchEquiv A.skeleton (A.family.placement j)).injective he))
      exact a1.trans (nodeSign_twist_lower (A.family.placement j))
    have hq1 : q ∈ (hj.newTree.plug (nodeSign ((P.srcJT con).chosen true).sig
        ((P.srcJT con).branches true (P.srcJT con).placement.lower).1) .leaf).branching := by
      rw [cross_lower P con]
      rw [hT'] at hq
      exact hq
    have w1 := P.T_tree_lj con hj q hq1
    rw [cross_lower P con] at w1
    have hdt : hj.data.tree (coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement j).lower) =
        hj.newTree := by
      have := finalData_tree_true P.srcJ hj.newTree hj.newCouple hj.tree_wf hj.couple_wf P.srcJ.placement.lower
      rw [if_pos rfl] at this
      exact this
    have hζ : nodeSign (unitTwistGarden A.skeleton (A.family.placement j)).sig
        (coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement j).lower).1 =
        nodeSign (P.opJT con hj).output.skeleton.sig ((P.srcJT con).branches true
          (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement j).lower)).1 :=
      (nodeSign_twist_lower (A.family.placement j)).trans hs1.symm
    have hq2 : q ∈ ((hj.data.tree (coreBranchEquiv A.skeleton (A.family.placement j)
        (A.family.placement j).lower)).plug (nodeSign (unitTwistGarden A.skeleton (A.family.placement j)).sig
          (coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement j).lower).1) .leaf).nodes := by
      rw [hdt, hζ]
      rw [hT'] at hq
      exact TTree.branching_subset_nodes _ hq
    have w2 := P.swap.T_tree_li hj con q hq2
    have hpos : inflatedPosition (unitTwistGarden A.skeleton (A.family.placement j)) hj.data.tree
        (coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement j).lower).toNode =
        (P.specT con hj).aT2 :=
      finalPos_eq (s := P.srcJ) (ε := true) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf
    have hr := congrArg (fun x => layerAt hj.output (addrExt x q)) hpos
    exact w1.trans (hr.symm.trans (w2.symm.trans hcg))
  · by_cases hbi : b = (A.family.placement i).lower
    · subst hbi
      have hT' : (P.opJT con hj).output.data.tree
          ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower)) =
          con.newTree := by
        refine hT.trans ?_
        rw [if_neg hbj, if_pos rfl]
      have hne2 : coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower ≠
          (A.family.nextPlacement i j).lower := by
        rw [CoreFamily.nextPlacement_lower]
        exact fun he => hbj ((coreBranchEquiv A.skeleton (A.family.placement i)).injective he)
      have hs1 : nodeSign (P.opJT con hj).output.skeleton.sig ((P.srcJT con).branches true
          (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower)).1 =
          nodeSign (unitTwistGarden A.skeleton (A.family.placement i)).sig
            (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower).1 :=
        nodeSign_twist_other (A.family.nextPlacement i j) _ hne2
      have hdt : con.data.tree (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower) =
          con.newTree := by
        have := finalData_tree_true P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf P.srcI.placement.lower
        rw [if_pos rfl] at this
        exact this
      have hq1 : q ∈ ((con.data.tree (coreBranchEquiv A.skeleton (A.family.placement i)
          (A.family.placement i).lower)).plug (nodeSign (unitTwistGarden A.skeleton (A.family.placement i)).sig
            (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower).1) .leaf).nodes := by
        rw [hdt, ← hs1]
        rw [hT'] at hq
        exact TTree.branching_subset_nodes _ hq
      have w1 := P.T_tree_li con hj q hq1
      have hq2 : q ∈ (con.newTree.plug (nodeSign ((P.swap.srcJT hj).chosen true).sig
          ((P.swap.srcJT hj).branches true (P.swap.srcJT hj).placement.lower).1) .leaf).branching := by
        rw [cross_lower P.swap hj]
        have hc := nodeSign_cast (P.TT_skel con hj) _ _ (doubleBranch_commute_addr (A := A) P.hij (A.family.placement i).lower)
        rw [hT'] at hq
        exact (congrArg (fun z => q ∈ (con.newTree.plug z .leaf).branching) hc).mp hq
      have w2 := P.swap.T_tree_lj hj con q hq2
      rw [cross_lower P.swap hj] at w2
      have hpos : inflatedPosition (unitTwistGarden A.skeleton (A.family.placement i)) con.data.tree
          (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower).toNode =
          (P.swap.specT hj con).aT2 :=
        finalPos_eq (s := P.srcI) (ε := true) con.newTree con.newCouple con.tree_wf con.couple_wf
      have hr := congrArg (fun x => layerAt con.output (addrExt x q)) hpos
      exact w1.trans (hr.trans (w2.symm.trans hcg))
    · have hT' : (P.opJT con hj).output.data.tree
          ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b)) = A.data.tree b := by
        refine hT.trans ?_
        rw [if_neg hbj, if_neg hbi]
      have hne2 : coreBranchEquiv A.skeleton (A.family.placement i) b ≠
          (A.family.nextPlacement i j).lower := by
        rw [CoreFamily.nextPlacement_lower]
        exact fun he => hbj ((coreBranchEquiv A.skeleton (A.family.placement i)).injective he)
      have hsign : nodeSign (P.opJT con hj).output.skeleton.sig
          ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b)).1 =
          nodeSign A.skeleton.sig b.1 :=
        (nodeSign_twist_other (A.family.nextPlacement i j) _ hne2).trans
          (nodeSign_twist_other (A.family.placement i) b hbi)
      rw [hT', hsign] at hq
      have hq2 := TTree.branching_subset_nodes _ hq
      have w1 := P.T_tree_other con hj b hbj hbi q hq2
      have w2 := P.swap.T_tree_other hj con b hbi hbj q hq2
      exact w1.trans (w2.symm.trans hcg)

end WaveTurbulence.Stage1
