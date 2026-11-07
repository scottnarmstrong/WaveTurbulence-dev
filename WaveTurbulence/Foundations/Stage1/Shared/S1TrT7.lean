/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrT6
public import WaveTurbulence.Foundations.Stage1.Shared.S1Cnt3
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

theorem PairCtx.core_pin_cross (con : LFConstruction P.srcI true) (b : GBranch A.skeleton.tree) :
    layerAt A.layered (A.data.corePosition b) =
      layerAt con.output (con.data.corePosition (coreBranchEquiv A.skeleton (A.family.placement i) b)) :=
  con.coreLayers b

theorem PairCtx.core_cross_of (con : LFConstruction P.srcI true) {x : GBranch A.skeleton.tree}
    {y : GBranch (unitTwistGarden A.skeleton (A.family.placement i)).tree}
    (h : y = coreBranchEquiv A.skeleton (A.family.placement i) x) :
    layerAt A.layered (A.data.corePosition x) = layerAt con.output (con.data.corePosition y) := by
  rw [h]; exact con.coreLayers x

@[expose] noncomputable def PairCtx.specT (con : LFConstruction P.srcI true) {ε : Bool}
    (hj : LFConstruction P.srcJ ε) : GlueSpec (P.srcJT con) ε where
  X := hj.newTree
  Q := hj.newCouple
  hX := hj.tree_wf
  hQ := hj.couple_wf
  Tm := midLayered hj
  To := hj.output
  aT := coupleRoot (P.srcJ.baseData ε) (P.srcJ.chosen_plain ε) (P.srcJ.pairs ε P.srcJ.exceptional) 0
  bT := coupleRoot (P.srcJ.baseData ε) (P.srcJ.chosen_plain ε) (P.srcJ.pairs ε P.srcJ.exceptional) 1
  aT2 := inflatedPosition (P.srcJ.chosen ε) (P.srcJ.baseData ε).tree
    (P.srcJ.branches ε P.srcJ.placement.lower).toNode
  t' := hj.tail
  embQ := hj.coupleInsertion.newEmbedding
  patQ := hj.coupleInsertion.pattern
  embX := by
    have := hj.treeInsertion.newEmbedding
    rw [← cross_zeta P con ε] at this
    exact this
  patX := by
    have := hj.treeInsertion.pattern
    rw [← cross_zeta P con ε] at this
    exact this
  hpa := by
    have e1 := (h_par_a hj).symm
    rw [coupleRoot_zero] at e1 ⊢
    rw [e1, par_base P.srcJ ε _ (exc_first_nonroot P.srcJ ε).1,
      par_base (P.srcJT con) ε _ (exc_first_nonroot (P.srcJT con) ε).1]
    exact P.core_cross_of con (((parent_first (P.srcJT con) ε _).trans (cross_cfFirst P con ε)).trans
      (congrArg _ (parent_first P.srcJ ε _).symm))
  hpb := by
    have e1 := (h_par_b hj).symm
    rw [coupleRoot_one] at e1 ⊢
    rw [e1, par_base P.srcJ ε _ (exc_first_nonroot P.srcJ ε).2,
      par_base (P.srcJT con) ε _ (exc_first_nonroot (P.srcJT con) ε).2]
    exact P.core_cross_of con (((parent_second (P.srcJT con) ε _).trans (cross_cfSecond P con ε)).trans
      (congrArg _ (parent_second P.srcJ ε _).symm))
  hpl := by
    have e1 := h_par_lower hj
    rw [e1, par_base P.srcJ ε _ (lower_nonroot P.srcJ ε),
      par_base (P.srcJT con) ε _ (lower_nonroot (P.srcJT con) ε)]
    exact P.core_cross_of con (((parent_low (P.srcJT con) ε _).trans (cross_cfLow P con ε)).trans
      (congrArg _ (parent_low P.srcJ ε _).symm))
  hlone := by
    have e1 := h_lone hj
    rw [e1]
    have h2 := con.coreLayers P.srcJ.placement.lower
    have e : P.srcI.branches true P.srcJ.placement.lower = (P.srcJT con).placement.lower :=
      (cross_lower P con).symm
    rw [e] at h2
    exact h2.trans (core_lower_pin (P.srcJT con) ε)
  hpm := (hj.coupleInsertion.canonical (P.srcJ.base_canonical ε)).criterion.1
  hpo := hj.canonical.criterion.1

end WaveTurbulence.Stage1
