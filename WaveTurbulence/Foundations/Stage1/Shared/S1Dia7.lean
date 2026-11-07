/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia6
import Mathlib.Tactic

/-!
# Class values of the transported output (after a `true` operation), for either choice of the second
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j) {ε : Bool}

theorem PairCtx.mem_tree_cross (con : LFConstruction P.srcI true) (b : GBranch A.skeleton.tree)
    (hbi : b ≠ (A.family.placement i).lower) (q : Path)
    (hq : q ∈ ((A.data.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).nodes) :
    q ∈ ((con.data.tree (coreBranchEquiv A.skeleton (A.family.placement i) b)).plug
      (nodeSign (unitTwistGarden A.skeleton (A.family.placement i)).sig
        (coreBranchEquiv A.skeleton (A.family.placement i) b).1) .leaf).nodes := by
  have ht : con.data.tree (coreBranchEquiv A.skeleton (A.family.placement i) b) = A.data.tree b :=
    data_tree_other_true con b hbi
  have hs := coreBranchEquiv_sign A.skeleton (A.family.placement i) b
  have hs' : nodeSign (unitTwistGarden A.skeleton (A.family.placement i)).sig
      (coreBranchEquiv A.skeleton (A.family.placement i) b).1 = nodeSign A.skeleton.sig b.1 := by
    split_ifs at hs with hc
    · exact absurd hc hbi
    · exact hs
  rw [ht, hs']
  exact hq

theorem PairCtx.T_core (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ ε)
    (b : GBranch A.skeleton.tree) :
    layerAt (P.constT con hj).output ((P.specT con hj).FD.corePosition
      ((P.srcJT con).branches ε (coreBranchEquiv A.skeleton (A.family.placement i) b))) =
      layerAt A.layered (A.data.corePosition b) :=
  (((P.specT con hj).pins (k2_pins _ _) (hplug_of _ _)).1 _).symm.trans (con.coreLayers b).symm

theorem PairCtx.T_tree_other (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ ε)
    (b : GBranch A.skeleton.tree) (hbj : b ≠ (A.family.placement j).lower)
    (hbi : b ≠ (A.family.placement i).lower) (q : Path)
    (hq : q ∈ ((A.data.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).nodes) :
    layerAt (P.constT con hj).output (addrExt (inflatedPosition ((P.srcJT con).chosen ε)
      (P.specT con hj).FD.tree ((P.srcJT con).branches ε
        (coreBranchEquiv A.skeleton (A.family.placement i) b)).toNode) q) =
      layerAt A.layered (addrExt (inflatedPosition A.skeleton A.data.tree b.toNode) q) := by
  have hne : coreBranchEquiv A.skeleton (A.family.placement i) b ≠ (P.srcJT con).placement.lower := by
    rw [cross_lower P con]
    exact fun he => hbj ((coreBranchEquiv A.skeleton (A.family.placement i)).injective he)
  have hq' := P.mem_tree_cross con b hbi q hq
  have h1 := ((P.specT con hj).pins (k2_pins _ _) (hplug_of _ _)).2.1 _ hne q hq'
  have h2 := con.ordinaryTreeLayers b hbi q hq
  exact h1.symm.trans h2.symm

theorem PairCtx.T_tree_li (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ ε) (q : Path)
    (hq : q ∈ ((con.data.tree (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower)).plug
      (nodeSign (unitTwistGarden A.skeleton (A.family.placement i)).sig
        (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower).1) .leaf).nodes) :
    layerAt (P.constT con hj).output (addrExt (inflatedPosition ((P.srcJT con).chosen ε)
      (P.specT con hj).FD.tree ((P.srcJT con).branches ε
        (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower)).toNode) q) =
      layerAt con.output (addrExt (inflatedPosition (unitTwistGarden A.skeleton (A.family.placement i))
        con.data.tree (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower).toNode) q) := by
  have hne : coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower ≠
      (P.srcJT con).placement.lower := by
    rw [cross_lower P con]
    exact fun he => P.lowerJ_ne ((coreBranchEquiv A.skeleton (A.family.placement i)).injective he).symm
  exact (((P.specT con hj).pins (k2_pins _ _) (hplug_of _ _)).2.1 _ hne q hq).symm

theorem PairCtx.T_tree_lj (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ ε) (q : Path)
    (hq : q ∈ (hj.newTree.plug (nodeSign ((P.srcJT con).chosen ε).sig
      ((P.srcJT con).branches ε (P.srcJT con).placement.lower).1) .leaf).branching) :
    layerAt (P.constT con hj).output (addrExt (inflatedPosition ((P.srcJT con).chosen ε)
      (P.specT con hj).FD.tree ((P.srcJT con).branches ε (P.srcJT con).placement.lower).toNode) q) =
      layerAt hj.output (addrExt (P.specT con hj).aT2 q) :=
  glue_region_tree (P.specT con hj) q hq

theorem PairCtx.T_couple_other (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ ε)
    (qq : SourcePair A.skeleton) (hqi : qq ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)
    (hqj : qq ≠ pairOfLeaf A.skeleton A.plain (A.family.placement j).retained) (j' : Fin 2) (r : Path)
    (hr : r ∈ ((decodedCouple (A.data.couple qq)).tree j').nodes) :
    layerAt (P.constT con hj).output (addrExt (coupleRoot (P.specT con hj).FD ((P.srcJT con).chosen_plain ε)
      ((P.srcJT con).pairs ε (P.srcI.pairs true qq)) j') r) =
      layerAt A.layered (addrExt (coupleRoot A.data A.plain qq j') r) := by
  have hco : con.data.couple (P.srcI.pairs true qq) = A.data.couple qq := data_couple_other_true con qq hqi
  have hr' : r ∈ ((decodedCouple ((P.srcJT con).data.couple (P.srcI.pairs true qq))).tree j').nodes := by
    change r ∈ ((decodedCouple (con.data.couple (P.srcI.pairs true qq))).tree j').nodes
    rw [hco]; exact hr
  have hne : P.srcI.pairs true qq ≠ (P.srcJT con).exceptional := by
    rw [P.exc_cross con]
    exact fun he => hqj ((P.srcI.pairs true).injective he)
  have h1 := ((P.specT con hj).pins (k2_pins _ _) (hplug_of _ _)).2.2 _ hne j' r hr'
  have h2 := con.ordinaryCoupleLayers qq hqi j' r hr
  exact h1.symm.trans h2.symm

theorem PairCtx.T_couple_ei (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ ε)
    (j' : Fin 2) (r : Path)
    (hr : r ∈ ((decodedCouple (con.data.couple (P.srcI.pairs true P.srcI.exceptional))).tree j').nodes) :
    layerAt (P.constT con hj).output (addrExt (coupleRoot (P.specT con hj).FD ((P.srcJT con).chosen_plain ε)
      ((P.srcJT con).pairs ε (P.srcI.pairs true P.srcI.exceptional)) j') r) =
      layerAt con.output (addrExt (coupleRoot con.data (P.srcI.chosen_plain true)
        (P.srcI.pairs true P.srcI.exceptional) j') r) := by
  have hne : P.srcI.pairs true P.srcI.exceptional ≠ (P.srcJT con).exceptional := by
    rw [P.exc_cross con]
    exact fun he => P.excJ_ne ((P.srcI.pairs true).injective he).symm
  exact (((P.specT con hj).pins (k2_pins _ _) (hplug_of _ _)).2.2 _ hne j' r hr).symm

theorem PairCtx.T_couple_ej (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ ε)
    (j' : Fin 2) (r : Path) :
    layerAt (P.constT con hj).output (addrExt (coupleRoot (P.specT con hj).FD ((P.srcJT con).chosen_plain ε)
      ((P.srcJT con).pairs ε (P.srcJT con).exceptional) j') r) =
      layerAt (midLayered hj) (addrExt (if j' = 0 then (P.specT con hj).aT else (P.specT con hj).bT) r) :=
  glue_region_couple (P.specT con hj) j' r

end WaveTurbulence.Stage1
