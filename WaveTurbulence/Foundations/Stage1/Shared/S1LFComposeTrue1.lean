/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue6
import Mathlib.Tactic

/-!
# Composition of a true-choice LF operation with a second operation at its output

Generic composition: a construction at the reverse source (choice `ε2`) composes with the first
`true`-choice construction to a construction at the original source with choice `!ε2`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

section Generic
variable {s : LFSource p kind LG} (h : LFConstruction s true)

theorem compose_midData_heq {ε2 : Bool}
    (hT : (revSourceT s h).chosen ε2 = s.chosen (!ε2))
    (hbaseD : HEq ((revSourceT s h).baseData ε2) (s.baseData (!ε2)))
    (hpr : ∀ q : SourcePair s.skeleton, ((revSourceT s h).pairs ε2 (s.pairs true q)).1 = (s.pairs (!ε2) q).1)
    (Q : RegCpl) (hQ : Q.wf = true) :
    HEq ((revSourceT s h).midData ε2 Q hQ) (s.midData (!ε2) Q hQ) := by
  unfold LFSource.midData
  refine withCouple_heq hT hbaseD ?_ Q hQ
  have e : (revSourceT s h).exceptional = s.pairs true s.exceptional := (pairs_true_exc s).symm
  rw [e]
  exact hpr s.exceptional

theorem compose_finalData_heq {ε2 : Bool}
    (hT : (revSourceT s h).chosen ε2 = s.chosen (!ε2))
    (hbaseD : HEq ((revSourceT s h).baseData ε2) (s.baseData (!ε2)))
    (hbr : ∀ b : GBranch s.skeleton.tree,
      ((revSourceT s h).branches ε2 (s.branches true b)).1 = (s.branches (!ε2) b).1)
    (hpr : ∀ q : SourcePair s.skeleton, ((revSourceT s h).pairs ε2 (s.pairs true q)).1 = (s.pairs (!ε2) q).1)
    (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true) :
    HEq ((revSourceT s h).finalData ε2 X Q hX hQ) (s.finalData (!ε2) X Q hX hQ) := by
  unfold LFSource.finalData
  exact withTree_heq hT (compose_midData_heq h hT hbaseD hpr Q hQ) (hbr s.placement.lower) X hX

/-- **Generic composition after a true-choice construction.** -/
theorem exists_compose_construction_true {ε2 : Bool} (h2 : LFConstruction (revSourceT s h) ε2)
    (hT : (revSourceT s h).chosen ε2 = s.chosen (!ε2))
    (hbase : (revSourceT s h).base ε2 = s.base (!ε2))
    (hbaseD : HEq ((revSourceT s h).baseData ε2) (s.baseData (!ε2)))
    (hbr : ∀ b : GBranch s.skeleton.tree,
      ((revSourceT s h).branches ε2 (s.branches true b)).1 = (s.branches (!ε2) b).1)
    (hpr : ∀ q : SourcePair s.skeleton, ((revSourceT s h).pairs ε2 (s.pairs true q)).1 = (s.pairs (!ε2) q).1) :
    ∃ h3 : LFConstruction s (!ε2), h3.output = h2.output ∧ HEq h3.data h2.data := by
  classical
  have e : (revSourceT s h).exceptional = s.pairs true s.exceptional := (pairs_true_exc s).symm
  have hbv : ((revSourceT s h).branches ε2 (revSourceT s h).placement.lower).1 =
      (s.branches (!ε2) s.placement.lower).1 := hbr s.placement.lower
  have hpv : ((revSourceT s h).pairs ε2 (revSourceT s h).exceptional).1 = (s.pairs (!ε2) s.exceptional).1 := by
    rw [e]
    exact hpr _
  have hmid2 := compose_midData_heq h hT hbaseD hpr h2.newCouple h2.couple_wf
  have hfin2 := compose_finalData_heq h hT hbaseD hbr hpr h2.newTree h2.newCouple h2.tree_wf h2.couple_wf
  have hmD : (s.midData (!ε2) h2.newCouple h2.couple_wf).Decodes (s.chosen_plain (!ε2))
      (midLayered h2).garden :=
    (decodes_heq hT hmid2 _ _ _).mp (((revSourceT s h).midData ε2 h2.newCouple h2.couple_wf).garden_decodes _)
  have heD : (s.finalData (!ε2) h2.newTree h2.newCouple h2.tree_wf h2.couple_wf).Decodes
      (s.chosen_plain (!ε2)) h2.output.garden :=
    (decodes_heq hT hfin2 _ _ _).mp h2.decodes
  let midLayer := decodedLayer (s.midData (!ε2) h2.newCouple h2.couple_wf) (s.chosen_plain (!ε2))
    (midLayered h2) hmD
  let outLayer := decodedLayer (s.finalData (!ε2) h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
    (s.chosen_plain (!ε2)) h2.output heD
  have hmL := decodedLayer_isLayering _ (s.chosen_plain (!ε2)) (midLayered h2) hmD
  have heL := decodedLayer_isLayering _ (s.chosen_plain (!ε2)) h2.output heD
  have hmidL : layeredReconstruction (s.midData (!ε2) h2.newCouple h2.couple_wf) (s.chosen_plain (!ε2))
      midLayer hmL = midLayered h2 := decodedLayered_eq _ _ _ hmD
  have houtL : layeredReconstruction (s.finalData (!ε2) h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
      (s.chosen_plain (!ε2)) outLayer heL = h2.output := decodedLayered_eq _ _ _ heD
  refine ⟨{
    newTree := h2.newTree
    newCouple := h2.newCouple
    tree_wf := h2.tree_wf
    couple_wf := h2.couple_wf
    midLayer := midLayer
    mid_isLayering := hmL
    outLayer := outLayer
    out_isLayering := heL
    tail := h2.tail
    coupleInsertion := ?_
    treeInsertion := ?_
    coreLayers := ?_
    ordinaryTreeLayers := ?_
    ordinaryCoupleLayers := ?_
    combinedOrder := ?_
    combinedTopCount := ?_ }, houtL, ?_⟩
  · have e0 : ∀ i, coupleRoot ((revSourceT s h).baseData ε2) ((revSourceT s h).chosen_plain ε2)
        ((revSourceT s h).pairs ε2 (revSourceT s h).exceptional) i =
        coupleRoot (s.baseData (!ε2)) (s.chosen_plain (!ε2)) (s.pairs (!ε2) s.exceptional) i :=
      fun i => coupleRoot_heq hT hbaseD _ _ hpv i
    rw [hmidL, ← hbase, ← e0 0, ← e0 1]
    exact h2.coupleInsertion
  · have epos : inflatedPosition ((revSourceT s h).chosen ε2)
        ((revSourceT s h).midData ε2 h2.newCouple h2.couple_wf).tree
        ((revSourceT s h).branches ε2 (revSourceT s h).placement.lower).toNode =
        inflatedPosition (s.chosen (!ε2)) (s.midData (!ε2) h2.newCouple h2.couple_wf).tree
        (s.branches (!ε2) s.placement.lower).toNode := inflatedPosition_heq hT hmid2 hbv
    have esign : nodeSign ((revSourceT s h).chosen ε2).sig
        ((revSourceT s h).branches ε2 (revSourceT s h).placement.lower).1 =
        nodeSign (s.chosen (!ε2)).sig (s.branches (!ε2) s.placement.lower).1 := by
      rw [congrArg Garden.sig hT, hbv]
    rw [hmidL, houtL, ← epos, ← esign]
    exact h2.treeInsertion
  · intro b
    rw [houtL]
    have e1 : ((revSourceT s h).finalData ε2 h2.newTree h2.newCouple h2.tree_wf h2.couple_wf).corePosition
        ((revSourceT s h).branches ε2 (s.branches true b)) =
        (s.finalData (!ε2) h2.newTree h2.newCouple h2.tree_wf h2.couple_wf).corePosition
        (s.branches (!ε2) b) := corePosition_heq hT hfin2 (hbr b)
    have k := h2.coreLayers (s.branches true b)
    rw [e1] at k
    exact (h.coreLayers b).trans k
  · intro b hb q hq
    rw [houtL]
    have hb' : s.branches true b ≠ (revSourceT s h).placement.lower :=
      fun he => hb ((s.branches true).injective he)
    have htree : h.data.tree (s.branches true b) = s.data.tree b := data_tree_other_gen h b hb
    have hsign : nodeSign (unitTwistGarden s.skeleton s.placement).sig (s.branches true b).1 =
        nodeSign s.skeleton.sig b.1 := ordinaryBranchSign_twist s.skeleton s.placement b hb
    have hq' : q ∈ (((revSourceT s h).data.tree (s.branches true b)).plug
        (nodeSign (revSourceT s h).skeleton.sig (s.branches true b).1) .leaf).nodes := by
      change q ∈ ((h.data.tree (s.branches true b)).plug
        (nodeSign (unitTwistGarden s.skeleton s.placement).sig (s.branches true b).1) .leaf).nodes
      rw [htree, hsign]
      exact hq
    have k1 := h.ordinaryTreeLayers b hb q hq
    have k2 := h2.ordinaryTreeLayers (s.branches true b) hb' q hq'
    have epos : inflatedPosition ((revSourceT s h).chosen ε2)
        ((revSourceT s h).finalData ε2 h2.newTree h2.newCouple h2.tree_wf h2.couple_wf).tree
        ((revSourceT s h).branches ε2 (s.branches true b)).toNode =
        inflatedPosition (s.chosen (!ε2))
        (s.finalData (!ε2) h2.newTree h2.newCouple h2.tree_wf h2.couple_wf).tree
        (s.branches (!ε2) b).toNode := inflatedPosition_heq hT hfin2 (hbr b)
    rw [epos] at k2
    exact k1.trans k2
  · intro q hq i r' hr
    rw [houtL]
    have hcpl : h.data.couple (s.pairs true q) = s.data.couple q := data_couple_other_gen h q hq
    have hr' : r' ∈ ((decodedCouple ((revSourceT s h).data.couple (s.pairs true q))).tree i).nodes := by
      change r' ∈ ((decodedCouple (h.data.couple (s.pairs true q))).tree i).nodes
      rw [hcpl]
      exact hr
    have hq' : s.pairs true q ≠ (revSourceT s h).exceptional :=
      fun he => hq ((s.pairs true).injective (he.trans e))
    have k1 := h.ordinaryCoupleLayers q hq i r' hr
    have k2 := h2.ordinaryCoupleLayers (s.pairs true q) hq' i r' hr'
    have epos : coupleRoot ((revSourceT s h).finalData ε2 h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
        ((revSourceT s h).chosen_plain ε2) ((revSourceT s h).pairs ε2 (s.pairs true q)) i =
        coupleRoot (s.finalData (!ε2) h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
        (s.chosen_plain (!ε2)) (s.pairs (!ε2) q) i := coupleRoot_heq hT hfin2 _ _ (hpr q) i
    rw [epos] at k2
    exact k1.trans k2
  · have e1' : (revSourceT s h).data.tree (revSourceT s h).placement.lower = h.newTree :=
      Function.update_self _ _ _
    have e2' : (revSourceT s h).data.couple (revSourceT s h).exceptional = h.newCouple := by
      rw [e]
      exact data_couple_exc h
    have k := h2.combinedOrder
    rw [e1', e2'] at k
    exact k.trans h.combinedOrder
  · rw [houtL]
    have key1 := h.combinedTopCount
    have key2 := h2.combinedTopCount
    have mid : rawTreeLayerCount h.output h.data (s.chosen_plain true) p (s.branches true s.placement.lower) +
        rawCoupleLayerCount h.output h.data (s.chosen_plain true) p (s.pairs true s.exceptional) =
        rawTreeLayerCount h.output (revSourceT s h).data (revSourceT s h).plain p
          (revSourceT s h).placement.lower +
        rawCoupleLayerCount h.output (revSourceT s h).data (revSourceT s h).plain p
          (revSourceT s h).exceptional := by
      rw [e]
      rfl
    have f1 : rawTreeLayerCount h2.output
        ((revSourceT s h).finalData ε2 h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
        ((revSourceT s h).chosen_plain ε2) p
        ((revSourceT s h).branches ε2 (revSourceT s h).placement.lower) =
        rawTreeLayerCount h2.output (s.finalData (!ε2) h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
        (s.chosen_plain (!ε2)) p (s.branches (!ε2) s.placement.lower) :=
      rawTreeLayerCount_heq hT hfin2 _ _ h2.output p hbv
    have f2 : rawCoupleLayerCount h2.output
        ((revSourceT s h).finalData ε2 h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
        ((revSourceT s h).chosen_plain ε2) p
        ((revSourceT s h).pairs ε2 (revSourceT s h).exceptional) =
        rawCoupleLayerCount h2.output (s.finalData (!ε2) h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
        (s.chosen_plain (!ε2)) p (s.pairs (!ε2) s.exceptional) :=
      rawCoupleLayerCount_heq hT hfin2 _ _ h2.output p hpv
    exact key1.trans (mid.trans (key2.trans (congrArg₂ (· + ·) f1 f2)))
  · exact hfin2.symm

end Generic


end WaveTurbulence.Stage1
