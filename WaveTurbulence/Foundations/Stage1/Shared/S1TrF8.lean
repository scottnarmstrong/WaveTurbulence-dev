/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cnt3
import Mathlib.Tactic

/-!
# Old-side counts and the order constraint across a `false`-choice operation at another member
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.lowerJ_ne : P.srcJ.placement.lower ≠ P.srcI.placement.lower :=
  fun he => P.hij (A.family.lower_injective he).symm

theorem PairCtx.excJ_ne : P.srcJ.exceptional ≠ P.srcI.exceptional :=
  CoreFamily.exceptional_ne A.family A.plain P.hij.symm

theorem PairCtx.data_tree_J (con : LFConstruction P.srcI false) :
    con.data.tree P.srcJ.placement.lower = P.srcJ.data.tree P.srcJ.placement.lower :=
  data_tree_other con _ P.lowerJ_ne

theorem PairCtx.data_couple_J (con : LFConstruction P.srcI false) :
    con.data.couple P.srcJ.exceptional = P.srcJ.data.couple P.srcJ.exceptional :=
  data_couple_other con _ P.excJ_ne

theorem PairCtx.hord_F (con : LFConstruction P.srcI false) {ε : Bool} (hj : LFConstruction P.srcJ ε) :
    hj.newTree.size + hj.newCouple.size =
      ((P.srcJF con).data.tree (P.srcJF con).placement.lower).size +
        ((P.srcJF con).data.couple (P.srcJF con).exceptional).size := by
  have := hj.combinedOrder
  rw [this]
  change _ = (con.data.tree P.srcJ.placement.lower).size + (con.data.couple P.srcJ.exceptional).size
  rw [P.data_tree_J con, P.data_couple_J con]

theorem PairCtx.old_count_F (con : LFConstruction P.srcI false) :
    rawTreeLayerCount con.output (P.srcJF con).data (P.srcJF con).plain p (P.srcJF con).placement.lower +
      rawCoupleLayerCount con.output (P.srcJF con).data (P.srcJF con).plain p (P.srcJF con).exceptional =
    rawTreeLayerCount A.layered P.srcJ.data P.srcJ.plain p P.srcJ.placement.lower +
      rawCoupleLayerCount A.layered P.srcJ.data P.srcJ.plain p P.srcJ.exceptional := by
  congr 1
  · rw [rawTreeLayerCount_eq, rawTreeLayerCount_eq]
    change ((((con.data.tree P.srcJ.placement.lower).plug _ .leaf).branching).filter _).card = _
    rw [P.data_tree_J con]
    congr 1
    refine Finset.filter_congr (fun q hq => ?_)
    have := con.ordinaryTreeLayers P.srcJ.placement.lower P.lowerJ_ne q (TTree.branching_subset_nodes _ hq)
    exact Iff.of_eq (congrArg (fun x => x = p) this.symm)
  · rw [rawCoupleLayerCount_eq, rawCoupleLayerCount_eq]
    change coupleSum (con.data.couple P.srcJ.exceptional) _ p = _
    rw [P.data_couple_J con]
    refine coupleSum_congr _ _ _ p (fun j' r hr => ?_)
    have := con.ordinaryCoupleLayers P.srcJ.exceptional P.excJ_ne j' r (TTree.branching_subset_nodes _ hr)
    have hpe : P.srcI.pairs false P.srcJ.exceptional = P.srcJ.exceptional :=
      LFSource.pairs_false P.srcI P.srcJ.exceptional
    rw [hpe] at this
    exact this.symm

/-- **Transport of a construction across a `false`-choice operation at another member.** -/
@[expose] noncomputable def PairCtx.constF (con : LFConstruction P.srcI false) {ε : Bool}
    (hj : LFConstruction P.srcJ ε) : LFConstruction (P.srcJF con) ε :=
  (P.specF con hj).construction (k2_pins _ ε) (hplug_of _ ε) (P.hord_F con hj)
    ((P.old_count_F con).trans (hj.combinedTopCount.trans
      ((new_count_of_h hj).trans (new_count_of_glue (P.specF con hj)).symm)))

end WaveTurbulence.Stage1
