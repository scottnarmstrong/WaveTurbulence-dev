/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia14
import Mathlib.Tactic

/-!
# Diamond for two `true` operations: couple classes
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.TT_castPair (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (qq : SourcePair A.skeleton) :
    castPair (P.TT_skel con hj) ((P.srcJT con).pairs true (P.srcI.pairs true qq)) =
      (P.swap.srcJT hj).pairs true (P.swap.srcI.pairs true qq) := by
  have hS1 : (P.opJT con hj).output.skeleton.IsPlain := (P.opJT con hj).output.plain
  have hS2 : (P.swap.opJT hj con).output.skeleton.IsPlain := (P.swap.opJT hj con).output.plain
  set ℓ := qq.firstLeaf A.plain with hℓ
  have hqq : qq = pairOfLeaf A.skeleton A.plain ℓ := (pairOfLeaf_firstLeaf A.skeleton A.plain qq).symm
  rw [hqq]
  have a1 : P.srcI.pairs true (pairOfLeaf A.skeleton A.plain ℓ) =
      pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i))
        (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement i) ℓ) :=
    sourcePairEquiv_pairOfLeaf P.srcI.plain (P.srcI.chosen_plain true) (chosenLeafEquiv _ _ true)
      (chosenLeafEquiv_pair _ _ true) ℓ
  have a2 : P.swap.srcI.pairs true (pairOfLeaf A.skeleton A.plain ℓ) =
      pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement j))
        (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement j) ℓ) :=
    sourcePairEquiv_pairOfLeaf P.swap.srcI.plain (P.swap.srcI.chosen_plain true) (chosenLeafEquiv _ _ true)
      (chosenLeafEquiv_pair _ _ true) ℓ
  rw [a1, a2]
  have b1 := sourcePairEquiv_pairOfLeaf (P.srcJT con).plain ((P.srcJT con).chosen_plain true)
    (chosenLeafEquiv (P.srcJT con).skeleton (P.srcJT con).placement true)
    (chosenLeafEquiv_pair (P.srcJT con).skeleton (P.srcJT con).placement true)
    (coreLeafEquiv A.skeleton (A.family.placement i) ℓ)
  have b2 := sourcePairEquiv_pairOfLeaf (P.swap.srcJT hj).plain ((P.swap.srcJT hj).chosen_plain true)
    (chosenLeafEquiv (P.swap.srcJT hj).skeleton (P.swap.srcJT hj).placement true)
    (chosenLeafEquiv_pair (P.swap.srcJT hj).skeleton (P.swap.srcJT hj).placement true)
    (coreLeafEquiv A.skeleton (A.family.placement j) ℓ)
  refine (congrArg (castPair (P.TT_skel con hj)) b1).trans (Eq.trans ?_ b2.symm)
  apply Subtype.ext
  exact sourcePairAt_cast (P.TT_skel con hj) _ _ (doubleLeaf_commute_addr (A := A) P.hij ℓ)

theorem PairCtx.TT_couple (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (qq : SourcePair A.skeleton) (j' : Fin 2) (r : Path)
    (hr : r ∈ (coupleForest ((P.opJT con hj).output.data.couple
      ((P.srcJT con).pairs true (P.srcI.pairs true qq))) j').branching) :
    layerAt (P.constT con hj).output (addrExt (coupleRoot (P.opJT con hj).output.data
      (P.opJT con hj).output.plain ((P.srcJT con).pairs true (P.srcI.pairs true qq)) j') r) =
    layerAt (P.swap.constT hj con).output (addrExt (coupleRoot (P.opJT con hj).output.data
      (P.opJT con hj).output.plain ((P.srcJT con).pairs true (P.srcI.pairs true qq)) j') r) := by
  have hcast := P.TT_castPair con hj qq
  have hxy : addrExt (coupleRoot (P.opJT con hj).output.data (P.opJT con hj).output.plain
      ((P.srcJT con).pairs true (P.srcI.pairs true qq)) j') r =
      addrExt (coupleRoot (P.swap.opJT hj con).output.data (P.swap.opJT hj con).output.plain
        ((P.swap.srcJT hj).pairs true (P.swap.srcI.pairs true qq)) j') r :=
    congrArg (fun x => addrExt x r) (coupleRoot_cast (P.TT_skel con hj) _ _ (P.TT_data_heq con hj) _ _ _ _
      (congrArg Subtype.val hcast) j')
  have hcg := congrArg (layerAt (P.swap.constT hj con).output) hxy.symm
  have hT := P.TT_FD_couple con hj qq
  have hne' : pairOfLeaf A.skeleton A.plain (A.family.placement i).retained ≠
      pairOfLeaf A.skeleton A.plain (A.family.placement j).retained := CoreFamily.exceptional_ne A.family A.plain P.hij
  by_cases hqj : qq = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained
  · rw [if_pos hqj] at hT
    subst hqj
    have hr' : r ∈ (coupleForest hj.newCouple j').branching := by rw [← hT]; exact hr
    have hr0 : r ∈ ((decodedCouple (hj.data.couple (P.srcJ.pairs true P.srcJ.exceptional))).tree j').nodes := by
      have hc : hj.data.couple (P.srcJ.pairs true P.srcJ.exceptional) = hj.newCouple := Function.update_self _ _ _
      rw [hc]; exact TTree.branching_subset_nodes _ hr'
    have w1 := P.T_couple_ej con hj j' r
    have w2 := P.swap.T_couple_ei hj con j' r hr0
    have w3 := h_couple_region hj j' r
    have e1 : (P.srcJT con).exceptional = P.srcI.pairs true P.srcJ.exceptional := P.exc_cross con
    have hlab1 := congrArg (fun x => layerAt (P.constT con hj).output
      (addrExt (coupleRoot (P.specT con hj).FD ((P.srcJT con).chosen_plain true)
        ((P.srcJT con).pairs true x) j') r)) e1.symm
    exact hlab1.trans (w1.trans (w3.symm.trans (w2.symm.trans hcg)))
  · by_cases hqi : qq = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
    · rw [if_neg hqj, if_pos hqi] at hT
      subst hqi
      have hr' : r ∈ (coupleForest con.newCouple j').branching := by rw [← hT]; exact hr
      have hr0 : r ∈ ((decodedCouple (con.data.couple (P.srcI.pairs true P.srcI.exceptional))).tree j').nodes := by
        have hc : con.data.couple (P.srcI.pairs true P.srcI.exceptional) = con.newCouple := Function.update_self _ _ _
        rw [hc]; exact TTree.branching_subset_nodes _ hr'
      have w1 := P.T_couple_ei con hj j' r hr0
      have w2 := P.swap.T_couple_ej hj con j' r
      have w3 := h_couple_region con j' r
      have e2 : (P.swap.srcJT hj).exceptional = P.srcJ.pairs true P.srcI.exceptional := P.swap.exc_cross hj
      have hlab2 := congrArg (fun x => layerAt (P.swap.constT hj con).output
        (addrExt (coupleRoot (P.swap.specT hj con).FD ((P.swap.srcJT hj).chosen_plain true)
          ((P.swap.srcJT hj).pairs true x) j') r)) e2
      have w3' : layerAt con.output (addrExt (coupleRoot con.data (P.srcI.chosen_plain true)
          (P.srcI.pairs true P.srcI.exceptional) j') r) = layerAt (midLayered con)
          (addrExt (if j' = 0 then (P.swap.specT hj con).aT else (P.swap.specT hj con).bT) r) := w3
      exact w1.trans (w3'.trans (w2.symm.trans (hlab2.symm.symm.trans hcg)))
    · rw [if_neg hqj, if_neg hqi] at hT
      have hr0 : r ∈ ((decodedCouple (A.data.couple qq)).tree j').nodes := by
        have hr' : r ∈ (coupleForest (A.data.couple qq) j').branching := by rw [← hT]; exact hr
        exact TTree.branching_subset_nodes _ hr'
      have w1 := P.T_couple_other con hj qq hqi hqj j' r hr0
      have w2 := P.swap.T_couple_other hj con qq hqj hqi j' r hr0
      exact w1.trans (w2.symm.trans hcg)

end WaveTurbulence.Stage1
