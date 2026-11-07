/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia1b
import Mathlib.Tactic

/-!
# Diamond for two `false`-choice operations: equality of the two final layered gardens
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.diamondFF_data (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false) :
    (show ReconstructionData A.skeleton from (P.specF con hj).FD) =
      (show ReconstructionData A.skeleton from (P.swap.specF hj con).FD) := by
  have hne : (A.family.placement i).lower ≠ (A.family.placement j).lower := CoreFamily.lower_ne_of_ne A.family P.hij
  have hne' : pairOfLeaf A.skeleton A.plain (A.family.placement i).retained ≠
      pairOfLeaf A.skeleton A.plain (A.family.placement j).retained := CoreFamily.exceptional_ne A.family A.plain P.hij
  apply ReconstructionData.ext_tree_couple
  · funext b
    have e1 : ((P.srcJF con).finalData false hj.newTree hj.newCouple hj.tree_wf hj.couple_wf).tree b =
        if b = (A.family.placement j).lower then hj.newTree else con.data.tree b :=
      finalData_tree_false (P.srcJF con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf b
    have e2 : ((P.swap.srcJF hj).finalData false con.newTree con.newCouple con.tree_wf con.couple_wf).tree b =
        if b = (A.family.placement i).lower then con.newTree else hj.data.tree b :=
      finalData_tree_false (P.swap.srcJF hj) con.newTree con.newCouple con.tree_wf con.couple_wf b
    have e3 : con.data.tree b = if b = (A.family.placement i).lower then con.newTree else A.data.tree b :=
      finalData_tree_false P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf b
    have e4 : hj.data.tree b = if b = (A.family.placement j).lower then hj.newTree else A.data.tree b :=
      finalData_tree_false P.srcJ hj.newTree hj.newCouple hj.tree_wf hj.couple_wf b
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [e3, e4]
    by_cases h1 : b = (A.family.placement j).lower
    · have h2 : b ≠ (A.family.placement i).lower := fun he => hne (he.symm.trans h1)
      rw [if_pos h1, if_neg h2, if_pos h1]
    · by_cases h2 : b = (A.family.placement i).lower
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
  · funext q
    have e1 : ((P.srcJF con).finalData false hj.newTree hj.newCouple hj.tree_wf hj.couple_wf).couple q =
        if q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained then hj.newCouple
          else con.data.couple q :=
      finalData_couple_false (P.srcJF con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf q
    have e2 : ((P.swap.srcJF hj).finalData false con.newTree con.newCouple con.tree_wf con.couple_wf).couple q =
        if q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained then con.newCouple
          else hj.data.couple q :=
      finalData_couple_false (P.swap.srcJF hj) con.newTree con.newCouple con.tree_wf con.couple_wf q
    have e3 : con.data.couple q = if q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
        then con.newCouple else A.data.couple q :=
      finalData_couple_false P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf q
    have e4 : hj.data.couple q = if q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained
        then hj.newCouple else A.data.couple q :=
      finalData_couple_false P.srcJ hj.newTree hj.newCouple hj.tree_wf hj.couple_wf q
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [e3, e4]
    by_cases h1 : q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained
    · have h2 : q ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained := fun he => hne' (he.symm.trans h1)
      rw [if_pos h1, if_neg h2, if_pos h1]
    · by_cases h2 : q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

theorem PairCtx.diamondFF_coreL (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (b : GBranch A.skeleton.tree) :
    layerAt (P.constF con hj).output ((P.specF con hj).FD.corePosition b) =
      layerAt A.layered (A.data.corePosition b) :=
  (((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).1 b).symm.trans (con.coreLayers b).symm

theorem PairCtx.diamondFF_coreR (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (b : GBranch A.skeleton.tree) :
    layerAt (P.swap.constF hj con).output ((P.swap.specF hj con).FD.corePosition b) =
      layerAt A.layered (A.data.corePosition b) :=
  (((P.swap.specF hj con).pins (k2_pins _ _) (hplug_of _ _)).1 b).symm.trans (hj.coreLayers b).symm

theorem PairCtx.hD' (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false) :
    (P.specF con hj).FD = (P.swap.specF hj con).FD := P.diamondFF_data con hj

theorem PairCtx.treeOtherL (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (b : GBranch A.skeleton.tree) (hbj : b ≠ (A.family.placement j).lower)
    (hbi : b ≠ (A.family.placement i).lower) (q : Path)
    (hq : q ∈ ((A.data.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).nodes) :
    layerAt (P.constF con hj).output (addrExt (inflatedPosition A.skeleton (P.specF con hj).FD.tree b.toNode) q) =
      layerAt A.layered (addrExt (inflatedPosition A.skeleton A.data.tree b.toNode) q) := by
  have hX : con.data.tree b = A.data.tree b := data_tree_other con b hbi
  have hq' : q ∈ (((P.srcJF con).data.tree b).plug (nodeSign (P.srcJF con).skeleton.sig b.1) .leaf).nodes := by
    change q ∈ ((con.data.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).nodes
    rw [hX]; exact hq
  have h1 := ((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).2.1 b hbj q hq'
  have h2 := con.ordinaryTreeLayers b hbi q hq
  exact h1.symm.trans (h2.symm)

theorem PairCtx.W1_li (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false) (q : Path)
    (hq : q ∈ ((con.data.tree (A.family.placement i).lower).plug
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1) .leaf).nodes) :
    layerAt (P.constF con hj).output (addrExt (inflatedPosition A.skeleton (P.specF con hj).FD.tree
      (A.family.placement i).lower.toNode) q) =
      layerAt con.output (addrExt (inflatedPosition A.skeleton con.data.tree (A.family.placement i).lower.toNode) q) := by
  have hbj : (A.family.placement i).lower ≠ (P.srcJF con).placement.lower :=
    CoreFamily.lower_ne_of_ne A.family P.hij
  exact (((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).2.1 _ hbj q hq).symm

theorem PairCtx.W1_lj (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false) (q : Path)
    (hq : q ∈ (hj.newTree.plug (nodeSign A.skeleton.sig (A.family.placement j).lower.1) .leaf).branching) :
    layerAt (P.constF con hj).output (addrExt (inflatedPosition A.skeleton (P.specF con hj).FD.tree
      (A.family.placement j).lower.toNode) q) =
      layerAt hj.output (addrExt (inflatedPosition A.skeleton hj.data.tree (A.family.placement j).lower.toNode) q) := by
  have h1 := glue_region_tree (P.specF con hj) q hq
  have h2 : inflatedPosition A.skeleton hj.data.tree (A.family.placement j).lower.toNode =
      (P.specF con hj).aT2 := finalPos_eq (s := P.srcJ) (ε := false) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf
  rw [h2]
  exact h1

theorem PairCtx.FD_tree_eq (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (b : GBranch A.skeleton.tree) :
    (P.specF con hj).FD.tree b = if b = (A.family.placement j).lower then hj.newTree
      else if b = (A.family.placement i).lower then con.newTree else A.data.tree b := by
  have e1 : ((P.srcJF con).finalData false hj.newTree hj.newCouple hj.tree_wf hj.couple_wf).tree b =
      if b = (A.family.placement j).lower then hj.newTree else con.data.tree b :=
    finalData_tree_false (P.srcJF con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf b
  have e3 : con.data.tree b = if b = (A.family.placement i).lower then con.newTree else A.data.tree b :=
    finalData_tree_false P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf b
  exact e1.trans (by rw [e3])

theorem PairCtx.diamondFF_tree (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (b : GBranch A.skeleton.tree) (q : Path)
    (hq : q ∈ (((P.specF con hj).FD.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).branching) :
    layerAt (P.constF con hj).output (addrExt (inflatedPosition A.skeleton (P.specF con hj).FD.tree b.toNode) q) =
      layerAt (P.swap.constF hj con).output
        (addrExt (inflatedPosition A.skeleton (P.specF con hj).FD.tree b.toNode) q) := by
  have hD' := P.hD' con hj
  have hxy : addrExt (inflatedPosition A.skeleton (P.specF con hj).FD.tree b.toNode) q =
      addrExt (inflatedPosition A.skeleton (P.swap.specF hj con).FD.tree b.toNode) q := by
    have := congrArg (fun E : ReconstructionData A.skeleton => addrExt (inflatedPosition A.skeleton E.tree b.toNode) q) hD'
    exact this
  have hcg := congrArg (layerAt (P.swap.constF hj con).output) hxy.symm
  have hT := P.FD_tree_eq con hj b
  by_cases hbj : b = (A.family.placement j).lower
  · rw [if_pos hbj] at hT
    subst hbj
    have hq1 : q ∈ (hj.newTree.plug (nodeSign A.skeleton.sig (A.family.placement j).lower.1) .leaf).branching := by
      rw [hT] at hq; exact hq
    have w1 := P.W1_lj con hj q hq1
    have hdt : hj.data.tree (A.family.placement j).lower = hj.newTree := Function.update_self _ _ _
    have hq2 : q ∈ ((hj.data.tree (A.family.placement j).lower).plug
        (nodeSign A.skeleton.sig (A.family.placement j).lower.1) .leaf).nodes := by
      rw [hdt]; exact TTree.branching_subset_nodes _ hq1
    have w2 := P.swap.W1_li hj con q hq2
    exact w1.trans (w2.symm.trans hcg)
  · by_cases hbi : b = (A.family.placement i).lower
    · rw [if_neg hbj, if_pos hbi] at hT
      subst hbi
      have hq1 : q ∈ (con.newTree.plug (nodeSign A.skeleton.sig (A.family.placement i).lower.1) .leaf).branching := by
        rw [hT] at hq; exact hq
      have hdt : con.data.tree (A.family.placement i).lower = con.newTree := Function.update_self _ _ _
      have hq2 : q ∈ ((con.data.tree (A.family.placement i).lower).plug
          (nodeSign A.skeleton.sig (A.family.placement i).lower.1) .leaf).nodes := by
        rw [hdt]; exact TTree.branching_subset_nodes _ hq1
      have w1 := P.W1_li con hj q hq2
      have w2 := P.swap.W1_lj hj con q hq1
      exact w1.trans (w2.symm.trans hcg)
    · rw [if_neg hbj, if_neg hbi] at hT
      have hq2 : q ∈ ((A.data.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).nodes := by
        rw [hT] at hq; exact TTree.branching_subset_nodes _ hq
      have w1 := P.treeOtherL con hj b hbj hbi q hq2
      have w2 := P.swap.treeOtherL hj con b hbi hbj q hq2
      exact w1.trans (w2.symm.trans hcg)

theorem PairCtx.C1_ei (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (j' : Fin 2) (r : Path)
    (hr : r ∈ ((decodedCouple (con.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained))).tree j').nodes) :
    layerAt (P.constF con hj).output (addrExt (coupleRoot (P.specF con hj).FD A.plain
      (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) j') r) =
      layerAt con.output (addrExt (coupleRoot con.data A.plain
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) j') r) := by
  have hq : pairOfLeaf A.skeleton A.plain (A.family.placement i).retained ≠ (P.srcJF con).exceptional :=
    fun he => P.excJ_ne he.symm
  have := ((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).2.2 _ hq j' r hr
  have hpe : (P.srcJF con).pairs false (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) =
      pairOfLeaf A.skeleton A.plain (A.family.placement i).retained :=
    LFSource.pairs_false (P.srcJF con) _
  rw [hpe] at this
  exact this.symm

theorem PairCtx.C1_ej (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (j' : Fin 2) (r : Path) :
    layerAt (P.constF con hj).output (addrExt (coupleRoot (P.specF con hj).FD A.plain
      (pairOfLeaf A.skeleton A.plain (A.family.placement j).retained) j') r) =
      layerAt hj.output (addrExt (coupleRoot hj.data A.plain
        (pairOfLeaf A.skeleton A.plain (A.family.placement j).retained) j') r) := by
  have h1 := glue_region_couple (P.specF con hj) j' r
  have h2 := h_couple_region hj j' r
  have hpe : (P.srcJF con).pairs false (P.srcJF con).exceptional = (P.srcJF con).exceptional :=
    LFSource.pairs_false (P.srcJF con) _
  have hpe' : P.srcJ.pairs false P.srcJ.exceptional = P.srcJ.exceptional := LFSource.pairs_false P.srcJ _
  have e1 : coupleRoot (P.specF con hj).FD (P.srcJF con).plain ((P.srcJF con).pairs false (P.srcJF con).exceptional) j' =
      coupleRoot (P.specF con hj).FD A.plain (P.srcJF con).exceptional j' := by rw [hpe]
  have e2 : coupleRoot hj.data P.srcJ.plain (P.srcJ.pairs false P.srcJ.exceptional) j' =
      coupleRoot hj.data A.plain P.srcJ.exceptional j' := by rw [hpe']
  exact (congrArg (fun x => layerAt (P.constF con hj).output (addrExt x r)) e1.symm).trans
    (h1.trans (h2.symm.trans (congrArg (fun x => layerAt hj.output (addrExt x r)) e2)))

theorem PairCtx.couple_otherL (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (qq : SourcePair A.skeleton) (hqi : qq ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)
    (hqj : qq ≠ pairOfLeaf A.skeleton A.plain (A.family.placement j).retained) (j' : Fin 2) (r : Path)
    (hr : r ∈ ((decodedCouple (A.data.couple qq)).tree j').nodes) :
    layerAt (P.constF con hj).output (addrExt (coupleRoot (P.specF con hj).FD A.plain qq j') r) =
      layerAt A.layered (addrExt (coupleRoot A.data A.plain qq j') r) := by
  have hco : con.data.couple qq = A.data.couple qq := data_couple_other con qq hqi
  have hr' : r ∈ ((decodedCouple ((P.srcJF con).data.couple qq)).tree j').nodes := by
    change r ∈ ((decodedCouple (con.data.couple qq)).tree j').nodes
    rw [hco]; exact hr
  have h1 := ((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).2.2 qq hqj j' r hr'
  have h2 := con.ordinaryCoupleLayers qq hqi j' r hr
  have hpe : (P.srcJF con).pairs false qq = qq := LFSource.pairs_false (P.srcJF con) _
  have hpe2 : P.srcI.pairs false qq = qq := LFSource.pairs_false P.srcI _
  rw [hpe] at h1
  rw [hpe2] at h2
  exact h1.symm.trans h2.symm

theorem PairCtx.FD_couple_eq (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (q : SourcePair A.skeleton) :
    (P.specF con hj).FD.couple q =
      if q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained then hj.newCouple
      else if q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained then con.newCouple
      else A.data.couple q := by
  have e1 : ((P.srcJF con).finalData false hj.newTree hj.newCouple hj.tree_wf hj.couple_wf).couple q =
      if q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained then hj.newCouple
        else con.data.couple q :=
    finalData_couple_false (P.srcJF con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf q
  have e3 : con.data.couple q = if q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
      then con.newCouple else A.data.couple q :=
    finalData_couple_false P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf q
  exact e1.trans (by rw [e3])

theorem PairCtx.diamondFF_couple (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false)
    (qq : SourcePair A.skeleton) (j' : Fin 2) (r : Path)
    (hr : r ∈ (coupleForest ((P.specF con hj).FD.couple qq) j').branching) :
    layerAt (P.constF con hj).output (addrExt (coupleRoot (P.specF con hj).FD A.plain qq j') r) =
      layerAt (P.swap.constF hj con).output (addrExt (coupleRoot (P.specF con hj).FD A.plain qq j') r) := by
  have hD' := P.hD' con hj
  have hxy : addrExt (coupleRoot (P.specF con hj).FD A.plain qq j') r =
      addrExt (coupleRoot (P.swap.specF hj con).FD A.plain qq j') r :=
    congrArg (fun E : ReconstructionData A.skeleton => addrExt (coupleRoot E A.plain qq j') r) hD'
  have hcg := congrArg (layerAt (P.swap.constF hj con).output) hxy.symm
  have hT := P.FD_couple_eq con hj qq
  have hne' : pairOfLeaf A.skeleton A.plain (A.family.placement i).retained ≠
      pairOfLeaf A.skeleton A.plain (A.family.placement j).retained := CoreFamily.exceptional_ne A.family A.plain P.hij
  by_cases hqj : qq = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained
  · rw [if_pos hqj] at hT
    subst hqj
    have hr0 : r ∈ ((decodedCouple (hj.data.couple
        (pairOfLeaf A.skeleton A.plain (A.family.placement j).retained))).tree j').nodes := by
      have hc : hj.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement j).retained) = hj.newCouple := by
        have := data_couple_exc hj
        rwa [LFSource.pairs_false P.srcJ] at this
      rw [hc]
      rw [hT] at hr
      exact TTree.branching_subset_nodes _ hr
    have w1 := P.C1_ej con hj j' r
    have w2 := P.swap.C1_ei hj con j' r hr0
    exact w1.trans (w2.symm.trans hcg)
  · by_cases hqi : qq = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
    · rw [if_neg hqj, if_pos hqi] at hT
      subst hqi
      have hr0 : r ∈ ((decodedCouple (con.data.couple
          (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained))).tree j').nodes := by
        have hc : con.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) = con.newCouple := by
          have := data_couple_exc con
          rwa [LFSource.pairs_false P.srcI] at this
        rw [hc]
        rw [hT] at hr
        exact TTree.branching_subset_nodes _ hr
      have w1 := P.C1_ei con hj j' r hr0
      have w2 := P.swap.C1_ej hj con j' r
      exact w1.trans (w2.symm.trans hcg)
    · rw [if_neg hqj, if_neg hqi] at hT
      have hr0 : r ∈ ((decodedCouple (A.data.couple qq)).tree j').nodes := by
        rw [hT] at hr; exact TTree.branching_subset_nodes _ hr
      have w1 := P.couple_otherL con hj qq hqi hqj j' r hr0
      have w2 := P.swap.couple_otherL hj con qq hqj hqi j' r hr0
      exact w1.trans (w2.symm.trans hcg)

theorem PairCtx.diamondFF_layered (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false) :
    (P.constF con hj).output = (P.swap.constF hj con).output := by
  have hD' := P.hD' con hj
  have h1 : (P.specF con hj).FD.Decodes A.plain (P.constF con hj).output.garden := (P.constF con hj).decodes
  have h2 : (P.specF con hj).FD.Decodes A.plain (P.swap.constF hj con).output.garden := by
    have := (P.swap.constF hj con).decodes
    rw [hD']
    exact this
  refine layered_eq_of_classes (p := p) (P.specF con hj).FD A.plain _ _ h1 h2 (P.constF con hj).canonical.criterion
    (P.swap.constF hj con).canonical.criterion ?_ ?_ ?_
  · intro b
    have hxy := congrArg (fun E : ReconstructionData A.skeleton => E.corePosition b) (P.hD' con hj)
    exact (P.diamondFF_coreL con hj b).trans ((P.diamondFF_coreR con hj b).symm.trans
      (congrArg (layerAt (P.swap.constF hj con).output) hxy.symm))
  · intro b q hq
    exact P.diamondFF_tree con hj b q hq
  · intro qq j' r hr
    exact P.diamondFF_couple con hj qq j' r hr

end WaveTurbulence.Stage1
