/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia5
import Mathlib.Tactic

/-!
# Class values of the transported output (after a `false` operation), for either choice of the second
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j) {ε : Bool}

theorem PairCtx.F_core (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ ε)
    (b : GBranch A.skeleton.tree) :
    layerAt (P.constF con hj).output ((P.specF con hj).FD.corePosition ((P.srcJF con).branches ε b)) =
      layerAt A.layered (A.data.corePosition b) :=
  (((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).1 b).symm.trans (con.coreLayers b).symm

theorem PairCtx.F_tree_other (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ ε)
    (b : GBranch A.skeleton.tree) (hbj : b ≠ (A.family.placement j).lower)
    (hbi : b ≠ (A.family.placement i).lower) (q : Path)
    (hq : q ∈ ((A.data.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).nodes) :
    layerAt (P.constF con hj).output (addrExt (inflatedPosition ((P.srcJF con).chosen ε)
      (P.specF con hj).FD.tree ((P.srcJF con).branches ε b).toNode) q) =
      layerAt A.layered (addrExt (inflatedPosition A.skeleton A.data.tree b.toNode) q) := by
  have hX : con.data.tree b = A.data.tree b := data_tree_other con b hbi
  have hq' : q ∈ (((P.srcJF con).data.tree b).plug (nodeSign (P.srcJF con).skeleton.sig b.1) .leaf).nodes := by
    change q ∈ ((con.data.tree b).plug (nodeSign A.skeleton.sig b.1) .leaf).nodes
    rw [hX]; exact hq
  have h1 := ((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).2.1 b hbj q hq'
  have h2 := con.ordinaryTreeLayers b hbi q hq
  exact h1.symm.trans (h2.symm)

theorem PairCtx.F_tree_li (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ ε) (q : Path)
    (hq : q ∈ ((con.data.tree (A.family.placement i).lower).plug
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1) .leaf).nodes) :
    layerAt (P.constF con hj).output (addrExt (inflatedPosition ((P.srcJF con).chosen ε)
      (P.specF con hj).FD.tree ((P.srcJF con).branches ε (A.family.placement i).lower).toNode) q) =
      layerAt con.output (addrExt (inflatedPosition A.skeleton con.data.tree (A.family.placement i).lower.toNode) q) := by
  have hbj : (A.family.placement i).lower ≠ (P.srcJF con).placement.lower :=
    CoreFamily.lower_ne_of_ne A.family P.hij
  exact (((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).2.1 _ hbj q hq).symm

theorem PairCtx.F_tree_lj (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ ε) (q : Path)
    (hq : q ∈ (hj.newTree.plug (nodeSign ((P.srcJF con).chosen ε).sig
      ((P.srcJF con).branches ε (A.family.placement j).lower).1) .leaf).branching) :
    layerAt (P.constF con hj).output (addrExt (inflatedPosition ((P.srcJF con).chosen ε)
      (P.specF con hj).FD.tree ((P.srcJF con).branches ε (A.family.placement j).lower).toNode) q) =
      layerAt hj.output (addrExt (P.specF con hj).aT2 q) :=
  glue_region_tree (P.specF con hj) q hq

theorem PairCtx.F_couple_other (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ ε)
    (qq : SourcePair A.skeleton) (hqi : qq ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)
    (hqj : qq ≠ pairOfLeaf A.skeleton A.plain (A.family.placement j).retained) (j' : Fin 2) (r : Path)
    (hr : r ∈ ((decodedCouple (A.data.couple qq)).tree j').nodes) :
    layerAt (P.constF con hj).output (addrExt (coupleRoot (P.specF con hj).FD ((P.srcJF con).chosen_plain ε)
      ((P.srcJF con).pairs ε qq) j') r) =
      layerAt A.layered (addrExt (coupleRoot A.data A.plain qq j') r) := by
  have hco : con.data.couple qq = A.data.couple qq := data_couple_other con qq hqi
  have hr' : r ∈ ((decodedCouple ((P.srcJF con).data.couple qq)).tree j').nodes := by
    change r ∈ ((decodedCouple (con.data.couple qq)).tree j').nodes
    rw [hco]; exact hr
  have h1 := ((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).2.2 qq hqj j' r hr'
  have h2 := con.ordinaryCoupleLayers qq hqi j' r hr
  have hpe2 : P.srcI.pairs false qq = qq := LFSource.pairs_false P.srcI _
  rw [hpe2] at h2
  exact h1.symm.trans h2.symm

theorem PairCtx.F_couple_ei (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ ε)
    (j' : Fin 2) (r : Path)
    (hr : r ∈ ((decodedCouple (con.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained))).tree j').nodes) :
    layerAt (P.constF con hj).output (addrExt (coupleRoot (P.specF con hj).FD ((P.srcJF con).chosen_plain ε)
      ((P.srcJF con).pairs ε (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)) j') r) =
      layerAt con.output (addrExt (coupleRoot con.data A.plain
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) j') r) := by
  have hq : pairOfLeaf A.skeleton A.plain (A.family.placement i).retained ≠ (P.srcJF con).exceptional :=
    fun he => P.excJ_ne he.symm
  exact (((P.specF con hj).pins (k2_pins _ _) (hplug_of _ _)).2.2 _ hq j' r hr).symm

theorem PairCtx.F_couple_ej (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ ε)
    (j' : Fin 2) (r : Path) :
    layerAt (P.constF con hj).output (addrExt (coupleRoot (P.specF con hj).FD ((P.srcJF con).chosen_plain ε)
      ((P.srcJF con).pairs ε (P.srcJF con).exceptional) j') r) =
      layerAt (midLayered hj) (addrExt (if j' = 0 then (P.specF con hj).aT else (P.specF con hj).bT) r) :=
  glue_region_couple (P.specF con hj) j' r

end WaveTurbulence.Stage1
