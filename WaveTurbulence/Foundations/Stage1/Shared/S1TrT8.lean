/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrT7
import Mathlib.Tactic

/-!
# Order, old-side counts and the transported construction across a `true`-choice operation
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.exc_cross (con : LFConstruction P.srcI true) :
    (P.srcJT con).exceptional = P.srcI.pairs true P.srcJ.exceptional := by
  have h1 : (P.srcJT con).placement.retained =
      coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement j).retained :=
    CoreFamily.nextPlacement_retained A.family i j
  have h2 : P.srcI.pairs true P.srcJ.exceptional =
      pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i))
        (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement j).retained) :=
    sourcePairEquiv_pairOfLeaf P.srcI.plain (P.srcI.chosen_plain true) (chosenLeafEquiv _ _ true)
      (chosenLeafEquiv_pair _ _ true) _
  exact (congrArg (fun l => pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i))
    (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain) l) h1).trans h2.symm

theorem PairCtx.lowerJ_ne' : P.srcJ.placement.lower ≠ P.srcI.placement.lower := P.lowerJ_ne
theorem PairCtx.excJ_ne' : P.srcJ.exceptional ≠ P.srcI.exceptional := P.excJ_ne

theorem PairCtx.hord_T (con : LFConstruction P.srcI true) {ε : Bool} (hj : LFConstruction P.srcJ ε) :
    hj.newTree.size + hj.newCouple.size =
      ((P.srcJT con).data.tree (P.srcJT con).placement.lower).size +
        ((P.srcJT con).data.couple (P.srcJT con).exceptional).size := by
  have := hj.combinedOrder
  rw [this]
  change _ = (con.data.tree (P.srcJT con).placement.lower).size +
    (con.data.couple (P.srcJT con).exceptional).size
  rw [cross_lower P con, P.exc_cross con]
  have h1 : con.data.tree (P.srcI.branches true P.srcJ.placement.lower) = P.srcJ.data.tree P.srcJ.placement.lower :=
    data_tree_other_true con _ P.lowerJ_ne
  have h2 : con.data.couple (P.srcI.pairs true P.srcJ.exceptional) = P.srcJ.data.couple P.srcJ.exceptional :=
    data_couple_other_true con _ P.excJ_ne
  exact congrArg₂ (· + ·) (congrArg RegChain.size h1).symm (congrArg RegCpl.size h2).symm

theorem PairCtx.old_count_T (con : LFConstruction P.srcI true) :
    rawTreeLayerCount con.output (P.srcJT con).data (P.srcJT con).plain p (P.srcJT con).placement.lower +
      rawCoupleLayerCount con.output (P.srcJT con).data (P.srcJT con).plain p (P.srcJT con).exceptional =
    rawTreeLayerCount A.layered P.srcJ.data P.srcJ.plain p P.srcJ.placement.lower +
      rawCoupleLayerCount A.layered P.srcJ.data P.srcJ.plain p P.srcJ.exceptional := by
  congr 1
  · rw [rawTreeLayerCount_eq, rawTreeLayerCount_eq]
    have e : (P.srcJT con).placement.lower = P.srcI.branches true P.srcJ.placement.lower := cross_lower P con
    have hX : (P.srcJT con).data.tree (P.srcJT con).placement.lower = P.srcJ.data.tree P.srcJ.placement.lower := by
      rw [e]; exact data_tree_other_true con _ P.lowerJ_ne
    have hs : nodeSign (P.srcJT con).skeleton.sig (P.srcJT con).placement.lower.1 =
        nodeSign P.srcJ.skeleton.sig P.srcJ.placement.lower.1 := by
      have := cross_zeta P con false
      rw [nodeSign_branches_lower, nodeSign_branches_lower] at this
      simpa using this
    change ((((P.srcJT con).data.tree (P.srcJT con).placement.lower).plug
      (nodeSign (P.srcJT con).skeleton.sig (P.srcJT con).placement.lower.1) .leaf).branching.filter _).card = _
    rw [hX, hs]
    congr 1
    refine Finset.filter_congr (fun q hq => ?_)
    have := con.ordinaryTreeLayers P.srcJ.placement.lower P.lowerJ_ne q (TTree.branching_subset_nodes _ hq)
    rw [e]
    exact Iff.of_eq (congrArg (fun x => x = p) this.symm)
  · rw [rawCoupleLayerCount_eq, rawCoupleLayerCount_eq]
    have hX : (P.srcJT con).data.couple (P.srcJT con).exceptional = P.srcJ.data.couple P.srcJ.exceptional := by
      rw [P.exc_cross con]; exact data_couple_other_true con _ P.excJ_ne
    change coupleSum ((P.srcJT con).data.couple (P.srcJT con).exceptional) _ p = _
    rw [hX]
    refine coupleSum_congr _ _ _ p (fun j' r hr => ?_)
    have := con.ordinaryCoupleLayers P.srcJ.exceptional P.excJ_ne j' r (TTree.branching_subset_nodes _ hr)
    have e2 : (P.srcJT con).exceptional = P.srcI.pairs true P.srcJ.exceptional := P.exc_cross con
    rw [e2]
    exact this.symm

/-- **Transport of a construction across a `true`-choice operation at another member.** -/
@[expose] noncomputable def PairCtx.constT (con : LFConstruction P.srcI true) {ε : Bool}
    (hj : LFConstruction P.srcJ ε) : LFConstruction (P.srcJT con) ε :=
  (P.specT con hj).construction (k2_pins _ ε) (hplug_of _ ε) (P.hord_T con hj)
    ((P.old_count_T con).trans (hj.combinedTopCount.trans
      (((new_count_of_h hj).trans (by rw [← cross_zeta P con ε]; rfl)).trans
        (new_count_of_glue (P.specT con hj)).symm)))

end WaveTurbulence.Stage1
