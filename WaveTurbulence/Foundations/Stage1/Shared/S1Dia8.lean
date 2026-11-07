/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia7
import Mathlib.Tactic

/-!
# Diamond for a `false` operation at `i` and a `true` operation at `j`: the final layered gardens agree
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.FT_FD_tree (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ true)
    (b : GBranch A.skeleton.tree) :
    (P.specF con hj).FD.tree (coreBranchEquiv A.skeleton (A.family.placement j) b) =
      if b = (A.family.placement j).lower then hj.newTree
      else if b = (A.family.placement i).lower then con.newTree else A.data.tree b := by
  have e1 : ((P.srcJF con).finalData true hj.newTree hj.newCouple hj.tree_wf hj.couple_wf).tree
      (coreBranchEquiv A.skeleton (A.family.placement j) b) =
      if b = (A.family.placement j).lower then hj.newTree else con.data.tree b :=
    finalData_tree_true (P.srcJF con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf b
  have e3 : con.data.tree b = if b = (A.family.placement i).lower then con.newTree else A.data.tree b :=
    finalData_tree_false P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf b
  exact e1.trans (by rw [e3])

theorem PairCtx.FT_FD_couple (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ true)
    (q : SourcePair A.skeleton) :
    (P.specF con hj).FD.couple (P.srcJ.pairs true q) =
      if q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained then hj.newCouple
      else if q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained then con.newCouple
      else A.data.couple q := by
  have e1 : ((P.srcJF con).finalData true hj.newTree hj.newCouple hj.tree_wf hj.couple_wf).couple
      (P.srcJ.pairs true q) =
      if q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained then hj.newCouple
        else con.data.couple q :=
    finalData_couple_true (P.srcJF con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf q
  have e3 : con.data.couple q = if q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
      then con.newCouple else A.data.couple q :=
    finalData_couple_false P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf q
  exact e1.trans (by rw [e3])

theorem PairCtx.FT_core (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ true)
    (b : GBranch A.skeleton.tree) :
    layerAt (P.constF con hj).output ((P.specF con hj).FD.corePosition
      (coreBranchEquiv A.skeleton (A.family.placement j) b)) =
    layerAt (P.swap.constT hj con).output ((P.specF con hj).FD.corePosition
      (coreBranchEquiv A.skeleton (A.family.placement j) b)) := by
  have a1 := P.F_core con hj b
  have a2 := P.swap.T_core hj con b
  have hxy := congrArg (fun E : ReconstructionData (unitTwistGarden A.skeleton (A.family.placement j)) =>
    E.corePosition (coreBranchEquiv A.skeleton (A.family.placement j) b)) (P.diamondFT_data con hj)
  have hcg := congrArg (layerAt (P.swap.constT hj con).output) hxy.symm
  exact a1.trans (a2.symm.trans hcg)

theorem nodeSign_twist_other {G : Garden w} (Pl : CorePlacement G) (b : GBranch G.tree) (hb : b ≠ Pl.lower) :
    nodeSign (unitTwistGarden G Pl).sig (coreBranchEquiv G Pl b).1 = nodeSign G.sig b.1 := by
  have hs := coreBranchEquiv_sign G Pl b
  split_ifs at hs with hc
  · exact absurd hc hb
  · exact hs

theorem PairCtx.FT_tree (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ true)
    (b : GBranch A.skeleton.tree) (q : Path)
    (hq : q ∈ (((P.specF con hj).FD.tree (coreBranchEquiv A.skeleton (A.family.placement j) b)).plug
      (nodeSign (unitTwistGarden A.skeleton (A.family.placement j)).sig
        (coreBranchEquiv A.skeleton (A.family.placement j) b).1) .leaf).branching) :
    layerAt (P.constF con hj).output (addrExt (inflatedPosition (unitTwistGarden A.skeleton (A.family.placement j))
      (P.specF con hj).FD.tree (coreBranchEquiv A.skeleton (A.family.placement j) b).toNode) q) =
    layerAt (P.swap.constT hj con).output (addrExt (inflatedPosition (unitTwistGarden A.skeleton (A.family.placement j))
      (P.specF con hj).FD.tree (coreBranchEquiv A.skeleton (A.family.placement j) b).toNode) q) := by
  have hxy : addrExt (inflatedPosition (unitTwistGarden A.skeleton (A.family.placement j))
      (P.specF con hj).FD.tree (coreBranchEquiv A.skeleton (A.family.placement j) b).toNode) q =
      addrExt (inflatedPosition (unitTwistGarden A.skeleton (A.family.placement j))
      (P.swap.specT hj con).FD.tree (coreBranchEquiv A.skeleton (A.family.placement j) b).toNode) q :=
    congrArg (fun E : ReconstructionData (unitTwistGarden A.skeleton (A.family.placement j)) =>
      addrExt (inflatedPosition (unitTwistGarden A.skeleton (A.family.placement j)) E.tree
        (coreBranchEquiv A.skeleton (A.family.placement j) b).toNode) q) (P.diamondFT_data con hj)
  have hcg := congrArg (layerAt (P.swap.constT hj con).output) hxy.symm
  have hT := P.FT_FD_tree con hj b
  by_cases hbj : b = (A.family.placement j).lower
  · rw [if_pos hbj] at hT
    subst hbj
    rw [hT] at hq
    have w1 := P.F_tree_lj con hj q hq
    have hdt : hj.data.tree (coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement j).lower) =
        hj.newTree := by
      have := finalData_tree_true P.srcJ hj.newTree hj.newCouple hj.tree_wf hj.couple_wf P.srcJ.placement.lower
      rw [if_pos rfl] at this
      exact this
    have hq2 : q ∈ ((hj.data.tree (coreBranchEquiv A.skeleton (A.family.placement j)
        (A.family.placement j).lower)).plug (nodeSign (unitTwistGarden A.skeleton (A.family.placement j)).sig
          (coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement j).lower).1) .leaf).nodes := by
      rw [hdt]; exact TTree.branching_subset_nodes _ hq
    have w2 := P.swap.T_tree_li hj con q hq2
    have hpos : inflatedPosition (unitTwistGarden A.skeleton (A.family.placement j)) hj.data.tree
        (coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement j).lower).toNode =
        (P.specF con hj).aT2 :=
      finalPos_eq (s := P.srcJ) (ε := true) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf
    have hr := congrArg (fun x => layerAt hj.output (addrExt x q)) hpos
    exact w1.trans (hr.symm.trans (w2.symm.trans hcg))
  · by_cases hbi : b = (A.family.placement i).lower
    · rw [if_neg hbj, if_pos hbi] at hT
      subst hbi
      rw [hT] at hq
      have hdt : con.data.tree (A.family.placement i).lower = con.newTree := Function.update_self _ _ _
      have hnej : (A.family.placement i).lower ≠ (A.family.placement j).lower :=
        CoreFamily.lower_ne_of_ne A.family P.hij
      have hq1 : q ∈ ((con.data.tree (A.family.placement i).lower).plug
          (nodeSign A.skeleton.sig (A.family.placement i).lower.1) .leaf).nodes := by
        rw [hdt, ← nodeSign_twist_other (A.family.placement j) _ hnej]
        exact TTree.branching_subset_nodes _ hq
      have w1 := P.F_tree_li con hj q hq1
      have hq2 : q ∈ (con.newTree.plug (nodeSign ((P.swap.srcJT hj).chosen false).sig
          ((P.swap.srcJT hj).branches false (P.swap.srcJT hj).placement.lower).1) .leaf).branching := by
        rw [cross_lower P.swap hj]; exact hq
      have w2 := P.swap.T_tree_lj hj con q hq2
      rw [cross_lower P.swap hj] at w2
      have hpos : inflatedPosition A.skeleton con.data.tree (A.family.placement i).lower.toNode =
          (P.swap.specT hj con).aT2 :=
        finalPos_eq (s := P.srcI) (ε := false) con.newTree con.newCouple con.tree_wf con.couple_wf
      have hr := congrArg (fun x => layerAt con.output (addrExt x q)) hpos
      exact w1.trans (hr.trans (w2.symm.trans hcg))
    · rw [if_neg hbj, if_neg hbi] at hT
      rw [hT, nodeSign_twist_other _ b hbj] at hq
      have hq2 := TTree.branching_subset_nodes _ hq
      have w1 := P.F_tree_other con hj b hbj hbi q hq2
      have w2 := P.swap.T_tree_other hj con b hbi hbj q hq2
      exact w1.trans (w2.symm.trans hcg)

theorem PairCtx.FT_couple (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ true)
    (qq : SourcePair A.skeleton) (j' : Fin 2) (r : Path)
    (hr : r ∈ (coupleForest ((P.specF con hj).FD.couple (P.srcJ.pairs true qq)) j').branching) :
    layerAt (P.constF con hj).output (addrExt (coupleRoot (P.specF con hj).FD
      (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain) (P.srcJ.pairs true qq) j') r) =
    layerAt (P.swap.constT hj con).output (addrExt (coupleRoot (P.specF con hj).FD
      (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain) (P.srcJ.pairs true qq) j') r) := by
  have hD := P.diamondFT_data con hj
  have hxy : addrExt (coupleRoot (P.specF con hj).FD
      (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain) (P.srcJ.pairs true qq) j') r =
      addrExt (coupleRoot (P.swap.specT hj con).FD
      (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain) (P.srcJ.pairs true qq) j') r :=
    congrArg (fun E : ReconstructionData (unitTwistGarden A.skeleton (A.family.placement j)) =>
      addrExt (coupleRoot E (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain)
        (P.srcJ.pairs true qq) j') r) hD
  have hcg := congrArg (layerAt (P.swap.constT hj con).output) hxy.symm
  have hT := P.FT_FD_couple con hj qq
  have hpf : (P.swap.srcJT hj).pairs false (P.srcJ.pairs true qq) = P.srcJ.pairs true qq :=
    LFSource.pairs_false (P.swap.srcJT hj) _
  by_cases hqj : qq = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained
  · rw [if_pos hqj] at hT
    subst hqj
    rw [hT] at hr
    have w1 := P.F_couple_ej con hj j' r
    have hr0 : r ∈ ((decodedCouple (hj.data.couple (P.srcJ.pairs true P.srcJ.exceptional))).tree j').nodes := by
      have hc : hj.data.couple (P.srcJ.pairs true P.srcJ.exceptional) = hj.newCouple := Function.update_self _ _ _
      rw [hc]; exact TTree.branching_subset_nodes _ hr
    have w2 := P.swap.T_couple_ei hj con j' r hr0
    have w3 := h_couple_region hj j' r
    have hlab := congrArg (fun x => layerAt (P.swap.constT hj con).output
      (addrExt (coupleRoot (P.swap.specT hj con).FD
        (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain) x j') r)) hpf
    exact w1.trans (w3.symm.trans (w2.symm.trans (hlab.trans hcg)))
  · by_cases hqi : qq = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
    · rw [if_neg hqj, if_pos hqi] at hT
      subst hqi
      rw [hT] at hr
      have hr0 : r ∈ ((decodedCouple (con.data.couple P.srcI.exceptional)).tree j').nodes := by
        have hc : con.data.couple P.srcI.exceptional = con.newCouple := by
          have := data_couple_exc con
          rwa [LFSource.pairs_false P.srcI] at this
        rw [hc]; exact TTree.branching_subset_nodes _ hr
      have hr1 : r ∈ ((decodedCouple (con.data.couple (pairOfLeaf A.skeleton A.plain
          (A.family.placement i).retained))).tree j').nodes := hr0
      have w1 := P.F_couple_ei con hj j' r hr1
      have w2 := P.swap.T_couple_ej hj con j' r
      have w3 := h_couple_region con j' r
      have e1 : P.srcI.pairs false P.srcI.exceptional = P.srcI.exceptional :=
        LFSource.pairs_false P.srcI _
      have hc1 := congrArg (fun x => layerAt con.output (addrExt (coupleRoot con.data A.plain x j') r)) e1.symm
      have e2 : (P.swap.srcJT hj).pairs false (P.swap.srcJT hj).exceptional = (P.swap.srcJT hj).exceptional :=
        LFSource.pairs_false (P.swap.srcJT hj) _
      have e3 : (P.swap.srcJT hj).exceptional = P.srcJ.pairs true P.srcI.exceptional := P.swap.exc_cross hj
      have hlab := congrArg (fun x => layerAt (P.swap.constT hj con).output
        (addrExt (coupleRoot (P.swap.specT hj con).FD
          (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain) x j') r)) (e2.trans e3)
      exact w1.trans (hc1.trans (w3.trans (w2.symm.trans (hlab.trans hcg))))
    · rw [if_neg hqj, if_neg hqi] at hT
      have hr0 : r ∈ ((decodedCouple (A.data.couple qq)).tree j').nodes := by
        rw [hT] at hr; exact TTree.branching_subset_nodes _ hr
      have w1 := P.F_couple_other con hj qq hqi hqj j' r hr0
      have w2 := P.swap.T_couple_other hj con qq hqj hqi j' r hr0
      have hlab := congrArg (fun x => layerAt (P.swap.constT hj con).output
        (addrExt (coupleRoot (P.swap.specT hj con).FD
          (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain) x j') r)) hpf
      exact w1.trans (w2.symm.trans (hlab.trans hcg))

end WaveTurbulence.Stage1
