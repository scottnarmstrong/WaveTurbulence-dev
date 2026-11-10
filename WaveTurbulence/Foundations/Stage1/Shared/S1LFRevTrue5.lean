/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue4
import Mathlib.Tactic

/-!
# Reversal of a true-choice LF operation: the reverse construction
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

section Construction
variable {s : LFSource p kind LG}

theorem data_tree_other_gen {ε : Bool} (h : LFConstruction s ε) (b : GBranch s.skeleton.tree)
    (hb : b ≠ s.placement.lower) : h.data.tree (s.branches ε b) = s.data.tree b :=
  (Function.update_of_ne (fun he => hb ((s.branches ε).injective he)) _ _).trans (s.base_tree_other ε b hb)

theorem data_couple_other_gen {ε : Bool} (h : LFConstruction s ε) (q : SourcePair s.skeleton)
    (hq : q ≠ s.exceptional) : h.data.couple (s.pairs ε q) = s.data.couple q :=
  (Function.update_of_ne (fun he => hq ((s.pairs ε).injective he)) _ _).trans (s.base_couple_other ε q hq)

variable (h : LFConstruction s true)


theorem revSourceT_pairs_twice_val (q0 : SourcePair s.skeleton) :
    ((revSourceT s h).pairs true (s.pairs true q0)).1 = q0.1 := by
  have hq := sourcePairEquiv_twice s.plain (s.chosen_plain true) ((revSourceT s h).chosen_plain true)
    (coreLeafEquiv s.skeleton s.placement) (fun l => (unitTwistGarden_pair s.skeleton s.placement l).symm)
    (coreLeafEquiv _ (reversePlacement s.skeleton s.placement))
    (fun l => (unitTwistGarden_pair _ (reversePlacement s.skeleton s.placement) l).symm)
    (unitTwistGarden_involutive s.skeleton s.placement) (coreLeafEquiv_twice_val s.skeleton s.placement) q0
  have := (congrArg Subtype.val hq).trans (cast_pair_val (unitTwistGarden_involutive s.skeleton s.placement) q0)
  exact this

/-- **Reverse construction (choice `true`).** -/
theorem exists_reverse_construction_true :
    ∃ h' : LFConstruction (revSourceT s h) true, h'.output = LG ∧ HEq h'.data s.data := by
  classical
  let X := s.data.tree s.placement.lower
  let Q := s.data.couple s.exceptional
  let hX := s.data.tree_wf s.placement.lower
  let hQ := s.data.couple_wf s.exceptional
  have hT := unitTwistGarden_involutive s.skeleton s.placement
  have hmidH := revSourceT_midData_heq h Q hQ
  have hfinH := revSourceT_finalData_data_heq h
  have hbase := revSourceT_base_true h
  have hmD : ((revSourceT s h).midData true Q hQ).Decodes ((revSourceT s h).chosen_plain true) s.identityMid.garden :=
    (decodes_heq hT hmidH _ _ _).mpr s.identityMid_decodes
  have heD : ((revSourceT s h).finalData true X Q hX hQ).Decodes ((revSourceT s h).chosen_plain true) LG.garden :=
    (decodes_heq hT (revSourceT_finalData_heq h X Q hX hQ) _ _ _).mpr s.identity_output_decodes
  let midLayer := decodedLayer ((revSourceT s h).midData true Q hQ) ((revSourceT s h).chosen_plain true) s.identityMid hmD
  let outLayer := decodedLayer ((revSourceT s h).finalData true X Q hX hQ) ((revSourceT s h).chosen_plain true) LG heD
  have hmL := decodedLayer_isLayering ((revSourceT s h).midData true Q hQ) ((revSourceT s h).chosen_plain true) s.identityMid hmD
  have heL := decodedLayer_isLayering ((revSourceT s h).finalData true X Q hX hQ) ((revSourceT s h).chosen_plain true) LG heD
  have hmidL : layeredReconstruction ((revSourceT s h).midData true Q hQ) ((revSourceT s h).chosen_plain true) midLayer hmL = s.identityMid :=
    decodedLayered_eq _ _ _ hmD
  have houtL : layeredReconstruction ((revSourceT s h).finalData true X Q hX hQ) ((revSourceT s h).chosen_plain true) outLayer heL = LG :=
    decodedLayered_eq _ _ _ heD
  obtain ⟨t, ht⟩ := s.identity_tree_insertion
  have hcoup := s.identity_couple_insertion
  have hpv : (((revSourceT s h).pairs true (revSourceT s h).exceptional).1 = (s.pairs false s.exceptional).1) :=
    (revSourceT_pairs_val h).trans (congrArg Subtype.val (LFSource.pairs_false s s.exceptional)).symm
  have hbv : ((revSourceT s h).branches true (revSourceT s h).placement.lower).1 = (s.branches false s.placement.lower).1 :=
    revSourceT_branches_val h
  refine ⟨{
    newTree := X
    newCouple := Q
    tree_wf := hX
    couple_wf := hQ
    midLayer := midLayer
    mid_isLayering := hmL
    outLayer := outLayer
    out_isLayering := heL
    tail := t
    coupleInsertion := ?_
    treeInsertion := ?_
    coreLayers := ?_
    ordinaryTreeLayers := ?_
    ordinaryCoupleLayers := ?_
    combinedOrder := ?_
    combinedTopCount := ?_ }, houtL, ?_⟩
  · have e0 : ∀ i, coupleRoot ((revSourceT s h).baseData true) ((revSourceT s h).chosen_plain true)
        ((revSourceT s h).pairs true (revSourceT s h).exceptional) i =
        coupleRoot (s.baseData false) (s.chosen_plain false) (s.pairs false s.exceptional) i :=
      fun i => coupleRoot_heq hT (revSourceT_baseData_heq h) _ _ hpv i
    rw [hmidL, hbase, e0 0, e0 1]
    exact hcoup
  · have epos : inflatedPosition ((revSourceT s h).chosen true) ((revSourceT s h).midData true Q hQ).tree
        ((revSourceT s h).branches true (revSourceT s h).placement.lower).toNode =
        inflatedPosition (s.chosen false) (s.midData false Q hQ).tree
        (s.branches false s.placement.lower).toNode :=
      inflatedPosition_heq hT hmidH hbv
    have esign : nodeSign ((revSourceT s h).chosen true).sig
        ((revSourceT s h).branches true (revSourceT s h).placement.lower).1 =
        nodeSign (s.chosen false).sig (s.branches false s.placement.lower).1 := by
      show nodeSign s.skeleton.sig _ = nodeSign s.skeleton.sig _
      rw [hbv]
    rw [hmidL, houtL, epos, esign]
    exact ht
  · intro b
    obtain ⟨b0, rfl⟩ := (s.branches true).surjective b
    have hv : ((revSourceT s h).branches true (s.branches true b0)).1 = b0.1 :=
      coreBranchEquiv_twice_val s.skeleton s.placement b0
    have e : ((revSourceT s h).finalData true X Q hX hQ).corePosition
        ((revSourceT s h).branches true (s.branches true b0)) = s.data.corePosition b0 :=
      corePosition_heq hT hfinH hv
    rw [houtL, e]
    exact (h.coreLayers b0).symm
  · intro b hb q hq
    obtain ⟨b0, rfl⟩ := (s.branches true).surjective b
    have hb0 : b0 ≠ s.placement.lower := fun he => hb (by rw [he]; rfl)
    have htree : h.data.tree (s.branches true b0) = s.data.tree b0 := data_tree_other_gen h b0 hb0
    have hsign : nodeSign (unitTwistGarden s.skeleton s.placement).sig (s.branches true b0).1 =
        nodeSign s.skeleton.sig b0.1 := ordinaryBranchSign_twist s.skeleton s.placement b0 hb0
    have hq' : q ∈ ((s.data.tree b0).plug (nodeSign s.skeleton.sig b0.1) .leaf).nodes := by
      change q ∈ ((h.data.tree (s.branches true b0)).plug
        (nodeSign (unitTwistGarden s.skeleton s.placement).sig (s.branches true b0).1) .leaf).nodes at hq
      rw [htree, hsign] at hq
      exact hq
    have key := h.ordinaryTreeLayers b0 hb0 q hq'
    have hv : ((revSourceT s h).branches true (s.branches true b0)).1 = b0.1 :=
      coreBranchEquiv_twice_val s.skeleton s.placement b0
    have epos : inflatedPosition ((revSourceT s h).chosen true)
        ((revSourceT s h).finalData true X Q hX hQ).tree
        ((revSourceT s h).branches true (s.branches true b0)).toNode =
        inflatedPosition s.skeleton s.data.tree b0.toNode := inflatedPosition_heq hT hfinH hv
    rw [houtL, epos]
    exact key.symm
  · intro q hq i r' hr
    obtain ⟨q0, rfl⟩ := (s.pairs true).surjective q
    have hq0 : q0 ≠ s.exceptional := fun he => hq (by rw [he]; exact pairs_true_exc s)
    have hcpl : h.data.couple (s.pairs true q0) = s.data.couple q0 := data_couple_other_gen h q0 hq0
    have hr' : r' ∈ ((decodedCouple (s.data.couple q0)).tree i).nodes := by
      change r' ∈ ((decodedCouple (h.data.couple (s.pairs true q0))).tree i).nodes at hr
      rw [hcpl] at hr
      exact hr
    have key := h.ordinaryCoupleLayers q0 hq0 i r' hr'
    have epos : coupleRoot ((revSourceT s h).finalData true X Q hX hQ) ((revSourceT s h).chosen_plain true)
        ((revSourceT s h).pairs true (s.pairs true q0)) i = coupleRoot s.data s.plain q0 i :=
      coupleRoot_heq hT hfinH _ _ (revSourceT_pairs_twice_val h q0) i
    rw [houtL, epos]
    exact key.symm
  · have e1 : h.data.tree (s.branches true s.placement.lower) = h.newTree := Function.update_self _ _ _
    have e2 : h.data.couple (s.pairs true s.exceptional) = h.newCouple := data_couple_exc h
    show X.size + Q.size = (h.data.tree (s.branches true s.placement.lower)).size +
      (h.data.couple (pairOfLeaf (unitTwistGarden s.skeleton s.placement)
        (unitTwistGarden_plain s.skeleton s.placement s.plain)
        (coreLeafEquiv s.skeleton s.placement s.placement.retained))).size
    rw [← pairs_true_exc s, e1, e2]
    exact h.combinedOrder.symm
  · have key := h.combinedTopCount
    have e1 : rawTreeLayerCount LG ((revSourceT s h).finalData true X Q hX hQ) ((revSourceT s h).chosen_plain true) p
        ((revSourceT s h).branches true (revSourceT s h).placement.lower) =
        rawTreeLayerCount LG s.data s.plain p s.placement.lower :=
      rawTreeLayerCount_heq hT hfinH _ _ LG p (revSourceT_branches_val h)
    have e2 : rawCoupleLayerCount LG ((revSourceT s h).finalData true X Q hX hQ) ((revSourceT s h).chosen_plain true) p
        ((revSourceT s h).pairs true (revSourceT s h).exceptional) =
        rawCoupleLayerCount LG s.data s.plain p s.exceptional :=
      rawCoupleLayerCount_heq hT hfinH _ _ LG p (revSourceT_pairs_val h)
    have e3 : (revSourceT s h).exceptional = s.pairs true s.exceptional := (pairs_true_exc s).symm
    rw [houtL, e1, e2, e3]
    exact key.symm
  · exact hfinH

end Construction


end WaveTurbulence.Stage1
