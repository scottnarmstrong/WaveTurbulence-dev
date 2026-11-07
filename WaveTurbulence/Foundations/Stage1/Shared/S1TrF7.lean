/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrF6
import Mathlib.Tactic

/-!
# The glue specification across a `false`-choice operation at another member
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

/-- The template glue specification: transport `hj` (an LF construction at member `j` of `A`) across
the `false`-choice operation `con` at member `i`. -/
@[expose] noncomputable def PairCtx.specF (con : LFConstruction P.srcI false) {ε : Bool}
    (hj : LFConstruction P.srcJ ε) : GlueSpec (P.srcJF con) ε where
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
  embX := hj.treeInsertion.newEmbedding
  patX := hj.treeInsertion.pattern
  hpa := by
    have e1 := (h_par_a hj).symm
    rw [coupleRoot_zero] at e1 ⊢
    rw [e1, par_base P.srcJ ε _ (exc_first_nonroot P.srcJ ε).1,
      par_base (P.srcJF con) ε _ (exc_first_nonroot (P.srcJF con) ε).1]
    exact con.coreLayers _
  hpb := by
    have e1 := (h_par_b hj).symm
    rw [coupleRoot_one] at e1 ⊢
    rw [e1, par_base P.srcJ ε _ (exc_first_nonroot P.srcJ ε).2,
      par_base (P.srcJF con) ε _ (exc_first_nonroot (P.srcJF con) ε).2]
    exact con.coreLayers _
  hpl := by
    have e1 := h_par_lower hj
    rw [e1, par_base P.srcJ ε _ (lower_nonroot P.srcJ ε),
      par_base (P.srcJF con) ε _ (lower_nonroot (P.srcJF con) ε)]
    exact con.coreLayers _
  hlone := by
    have e1 := h_lone hj
    rw [e1]
    exact (con.coreLayers _).trans (core_lower_pin (P.srcJF con) ε)
  hpm := (hj.coupleInsertion.canonical (P.srcJ.base_canonical ε)).criterion.1
  hpo := hj.canonical.criterion.1

end WaveTurbulence.Stage1
