/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRev
import Mathlib.Tactic

/-!
# Composing LF operations at one member

Casting lemmas for the normalized bases and the composition of a `false`-choice construction with a
second construction at its output.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

theorem unitLayerTwist_congr {LG1 LG2 : LayeredGarden w} (e : LG1 = LG2)
    {P1 : CorePlacement LG1.garden} {P2 : CorePlacement LG2.garden}
    (hP : (congrArg LayeredGarden.garden e ▸ P1 : CorePlacement LG2.garden) = P2)
    (h1 : SameLowerLayer LG1 P1) (h2 : SameLowerLayer LG2 P2) :
    unitLayerTwist LG1 P1 h1 = unitLayerTwist LG2 P2 h2 := by
  subst e
  have : P1 = P2 := hP
  subst this
  rfl

theorem expandedPlacement_congr {S : Garden w} {D1 D2 : ReconstructionData S} (eD : D1 = D2)
    (hS : S.IsPlain) {G1 G2 : Garden w} (hd1 : D1.Decodes hS G1) (hd2 : D2.Decodes hS G2) (eG : G1 = G2)
    (P : CorePlacement S) (hq1 : D1.couple (pairOfLeaf S hS P.retained) = .triv)
    (hq2 : D2.couple (pairOfLeaf S hS P.retained) = .triv) :
    (eG ▸ expandedPlacement D1 hS hd1 P hq1 : CorePlacement G2) = expandedPlacement D2 hS hd2 P hq2 := by
  subst eD
  subst eG
  rfl

variable {s : LFSource p kind LG} (h : LFConstruction s false)
  (hel : SourceLayerEligible h.output h.data s.plain h.decodes s.placement s.vineType s.support s.upper)
  (htc : CohOn h.output ((h.data.tree s.placement.lower).linksAt (nodeSign s.skeleton.sig s.placement.lower.1)
      (inflatedPosition s.skeleton h.data.tree s.placement.lower.toNode)))
  (hcc : CohOn h.output ((h.data.couple (pairOfLeaf s.skeleton s.plain s.placement.retained)).linksAt
      (inflatedPosition s.skeleton h.data.tree
        ((pairOfLeaf s.skeleton s.plain s.placement.retained).firstLeaf s.plain).toNode)
      (inflatedPosition s.skeleton h.data.tree
        ((pairOfLeaf s.skeleton s.plain s.placement.retained).secondLeaf s.plain).toNode)))

theorem revSource_base_true : (revSource h hel htc hcc).base true = s.base true := by
  unfold LFSource.base normalizedChoiceLayered
  refine unitLayerTwist_congr ?_ ?_ _ _
  · exact revSource_base h hel htc hcc
  · have eD : normalizedData h.data s.placement.lower s.exceptional =
        normalizedData s.data s.placement.lower s.exceptional :=
      (LFSource.baseData_false (revSource h hel htc hcc)).symm.trans
        ((revSource_baseData h hel htc hcc).trans (LFSource.baseData_false s))
    exact expandedPlacement_congr eD _ _ _ _ _ _ _

theorem revSource_baseData_choice (ε : Bool) :
    (revSource h hel htc hcc).baseData ε = s.baseData ε := by
  cases ε
  · exact revSource_baseData h hel htc hcc
  · have eD : normalizedData h.data s.placement.lower s.exceptional =
        normalizedData s.data s.placement.lower s.exceptional :=
      (LFSource.baseData_false (revSource h hel htc hcc)).symm.trans
        ((revSource_baseData h hel htc hcc).trans (LFSource.baseData_false s))
    exact congrArg (fun D => transportReconstruction s.plain (s.chosen_plain true) (s.branches true)
      (chosenLeafEquiv s.skeleton s.placement true) (chosenLeafEquiv_pair s.skeleton s.placement true) D) eD

theorem revSource_base_choice (ε : Bool) : (revSource h hel htc hcc).base ε = s.base ε := by
  cases ε
  · exact revSource_base h hel htc hcc
  · exact revSource_base_true h hel htc hcc

variable {ε : Bool} (h2 : LFConstruction (revSource h hel htc hcc) ε)

theorem revSource_midData_choice (Q : RegCpl) (hQ : Q.wf = true) :
    (revSource h hel htc hcc).midData ε Q hQ = s.midData ε Q hQ := by
  unfold LFSource.midData
  rw [revSource_baseData_choice h hel htc hcc]
  rfl

theorem revSource_finalData_choice (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true) :
    (revSource h hel htc hcc).finalData ε X Q hX hQ = s.finalData ε X Q hX hQ := by
  unfold LFSource.finalData
  rw [revSource_midData_choice h hel htc hcc]
  rfl

/-- **Composition.** A second construction at the output of a `false`-choice construction composes to a
construction at the original source with the same choice. -/
theorem exists_compose_construction :
    ∃ h3 : LFConstruction s ε, h3.output = h2.output ∧ h3.data = h2.data := by
  classical
  let s' := revSource h hel htc hcc
  have hmid := revSource_midData_choice h hel htc hcc (ε := ε) h2.newCouple h2.couple_wf
  have hfin := revSource_finalData_choice h hel htc hcc (ε := ε) h2.newTree h2.newCouple h2.tree_wf h2.couple_wf
  have hbase := revSource_base_choice h hel htc hcc ε
  have hbd := revSource_baseData_choice h hel htc hcc ε
  have hmD : (s.midData ε h2.newCouple h2.couple_wf).Decodes (s.chosen_plain ε) (midLayered h2).garden := by
    rw [← hmid]
    exact (s'.midData ε h2.newCouple h2.couple_wf).garden_decodes _
  have heD : (s.finalData ε h2.newTree h2.newCouple h2.tree_wf h2.couple_wf).Decodes (s.chosen_plain ε)
      h2.output.garden := by
    rw [← hfin]
    exact h2.decodes
  let midLayer := decodedLayer (s.midData ε h2.newCouple h2.couple_wf) (s.chosen_plain ε) (midLayered h2) hmD
  let outLayer := decodedLayer (s.finalData ε h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
    (s.chosen_plain ε) h2.output heD
  have hmL := decodedLayer_isLayering _ (s.chosen_plain ε) (midLayered h2) hmD
  have heL := decodedLayer_isLayering _ (s.chosen_plain ε) h2.output heD
  have hmidL : layeredReconstruction (s.midData ε h2.newCouple h2.couple_wf) (s.chosen_plain ε) midLayer hmL =
      midLayered h2 := decodedLayered_eq _ _ _ hmD
  have houtL : layeredReconstruction (s.finalData ε h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
      (s.chosen_plain ε) outLayer heL = h2.output := decodedLayered_eq _ _ _ heD
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
    combinedTopCount := ?_ }, houtL, hfin.symm⟩
  · rw [hmidL, ← hbase, ← hbd]
    exact h2.coupleInsertion
  · rw [hmidL, houtL, ← hmid]
    exact h2.treeInsertion
  · intro b
    rw [houtL, ← hfin]
    exact (h.coreLayers b).trans (h2.coreLayers b)
  · intro b hb q hq
    rw [houtL, ← hfin]
    have htb : h.data.tree b = s.data.tree b := data_tree_other h b hb
    have hq' : q ∈ (((revSource h hel htc hcc).data.tree b).plug
        (nodeSign (revSource h hel htc hcc).skeleton.sig b.1) .leaf).nodes := by
      change q ∈ ((h.data.tree b).plug _ _).nodes
      rw [htb]
      exact hq
    exact (h.ordinaryTreeLayers b hb q hq).trans (h2.ordinaryTreeLayers b hb q hq')
  · intro q hq i r hr
    rw [houtL, ← hfin]
    have htq : h.data.couple q = s.data.couple q := data_couple_other h q hq
    have hr' : r ∈ ((decodedCouple ((revSource h hel htc hcc).data.couple q)).tree i).nodes := by
      change r ∈ ((decodedCouple (h.data.couple q)).tree i).nodes
      rw [htq]
      exact hr
    have k1 := h.ordinaryCoupleLayers q hq i r hr
    have k2 := h2.ordinaryCoupleLayers q hq i r hr'
    rw [LFSource.pairs_false s q] at k1
    exact k1.trans k2
  · have e1 : (revSource h hel htc hcc).data.tree (revSource h hel htc hcc).placement.lower = h.newTree :=
      Function.update_self _ _ _
    have e2 : (revSource h hel htc hcc).data.couple (revSource h hel htc hcc).exceptional = h.newCouple := by
      have := data_couple_exc h
      rwa [LFSource.pairs_false] at this
    have k := h2.combinedOrder
    rw [e1, e2] at k
    exact k.trans h.combinedOrder
  · rw [houtL, ← hfin]
    have key1 := h.combinedTopCount
    have hb' : s.branches false s.placement.lower = s.placement.lower := rfl
    have hp' : s.pairs false s.exceptional = s.exceptional := LFSource.pairs_false s s.exceptional
    rw [hb', hp'] at key1
    have key2 := h2.combinedTopCount
    have k1 : rawTreeLayerCount (layeredReconstruction (s.finalData false h.newTree h.newCouple h.tree_wf h.couple_wf)
          (s.chosen_plain false) h.outLayer h.out_isLayering)
          (s.finalData false h.newTree h.newCouple h.tree_wf h.couple_wf) (s.chosen_plain false) p
          s.placement.lower +
        rawCoupleLayerCount (layeredReconstruction (s.finalData false h.newTree h.newCouple h.tree_wf h.couple_wf)
          (s.chosen_plain false) h.outLayer h.out_isLayering)
          (s.finalData false h.newTree h.newCouple h.tree_wf h.couple_wf) (s.chosen_plain false) p
          s.exceptional =
        rawTreeLayerCount h.output (revSource h hel htc hcc).data s.plain p
          (revSource h hel htc hcc).placement.lower +
        rawCoupleLayerCount h.output (revSource h hel htc hcc).data s.plain p
          (revSource h hel htc hcc).exceptional := rfl
    have k3 : rawTreeLayerCount (layeredReconstruction ((revSource h hel htc hcc).finalData ε h2.newTree h2.newCouple
          h2.tree_wf h2.couple_wf) (s.chosen_plain ε) h2.outLayer h2.out_isLayering)
          ((revSource h hel htc hcc).finalData ε h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
          (s.chosen_plain ε) p ((revSource h hel htc hcc).branches ε (revSource h hel htc hcc).placement.lower) +
        rawCoupleLayerCount (layeredReconstruction ((revSource h hel htc hcc).finalData ε h2.newTree h2.newCouple
          h2.tree_wf h2.couple_wf) (s.chosen_plain ε) h2.outLayer h2.out_isLayering)
          ((revSource h hel htc hcc).finalData ε h2.newTree h2.newCouple h2.tree_wf h2.couple_wf)
          (s.chosen_plain ε) p ((revSource h hel htc hcc).pairs ε (revSource h hel htc hcc).exceptional) =
        rawTreeLayerCount h2.output ((revSource h hel htc hcc).finalData ε h2.newTree h2.newCouple
          h2.tree_wf h2.couple_wf) (s.chosen_plain ε) p (s.branches ε s.placement.lower) +
        rawCoupleLayerCount h2.output ((revSource h hel htc hcc).finalData ε h2.newTree h2.newCouple
          h2.tree_wf h2.couple_wf) (s.chosen_plain ε) p (s.pairs ε s.exceptional) := rfl
    exact key1.trans (k1.trans (key2.trans k3))

end WaveTurbulence.Stage1

namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- **Composition at one member, first operation with choice `false`.** -/
theorem exists_compose_op_false (A : FamilyReconstruction w ι) (i : ι)
    (c : CanonicalObject p kind A.layered)
    (el : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i)
      (A.family.kind i) (A.family.atoms i) (A.family.upper i))
    (tc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
    (cc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))
    (con : LFConstruction (A.source i c el tc cc) false)
    (op2 : FamilyOperation (p := p) (kind := kind)
      (FamilyOperation.output (⟨c, el, tc, cc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) i) :
    ∃ op3 : FamilyOperation (p := p) (kind := kind) A i, op3.output = op2.output := by
  obtain ⟨h3, ho, hd⟩ := exists_compose_construction con (eligible_output con) (treeCoherent_output con)
    (coupleCoherent_output con) op2.construction
  refine ⟨⟨c, el, tc, cc, op2.choice, h3⟩, ?_⟩
  apply familyReconstruction_ext
  · rfl
  · exact HEq.rfl
  · exact heq_of_eq hd
  · exact ho

end WaveTurbulence.Stage1
