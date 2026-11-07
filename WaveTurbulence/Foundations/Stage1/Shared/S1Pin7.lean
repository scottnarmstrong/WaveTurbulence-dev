/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Pin6
public import WaveTurbulence.Foundations.Stage1.Shared.S1LFCompose
public import WaveTurbulence.Foundations.Molecule.LFTwist.LayeredReconstructedUnit
import Mathlib.Tactic

/-!
# K2 for the choice `true` (unit twist coordinates)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

/-- Layer of the unit twist at an exchanged address, for an arbitrary decoded layered garden. -/
theorem eu_layer {S : Garden w} (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)
    (hnil : D.tree P.lower = .nil) (N0 : LayeredGarden w) (hd : D.Decodes hS N0.garden)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    (he : SameLowerLayer N0 (expandedPlacement D hS hd P hq)) (z : Address w)
    (hz : z.2 ∈ (N0.garden.tree z.1).nodes) :
    layerAt (unitLayerTwist N0 (expandedPlacement D hS hd P hq) he) (inflatedExchange S P D z) =
      layerAt N0 z := by
  obtain ⟨G0, l0, hl0⟩ := N0
  have hg : G0 = D.garden hS := rawOfGarden_injective_plain hd.1 (D.garden_plain hS)
    (hd.2.symm.trans (D.garden_raw hS).symm)
  subst hg
  have := erasedUnit_layerAt S P hS D l0 hl0 hnil hq he ⟨z, hz⟩
  exact this.trans (layerAt_of_mem (layeredReconstruction D hS l0 hl0) hz).symm

theorem chain_node_mem_forest {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (b : GBranch S.tree) (q : Path) (hq : q ∈ ((D.tree b).plug (nodeSign S.sig b.1) .leaf).nodes) :
    (addrExt (inflatedPosition S D.tree b.toNode) q).2 ∈
      ((D.forest hS) (addrExt (inflatedPosition S D.tree b.toNode) q).1).nodes := by
  have hs := (D.forest_subtree_position hS b.toNode).trans (congrArg some (D.inflateNode_branch hS b))
  exact (Comb.subtree_nodes_iff hs q).mp (chain_nodes_subset_plug _ _ _ hq)

theorem k2_true (s : LFSource p kind LG) : K2Pins s true := by
  classical
  have hk := k2_normalized (p := p) LG s.data s.plain s.decodes s.placement.lower s.exceptional s.canonical
    s.treeCoherent
  set ND := normalizedData s.data s.placement.lower s.exceptional with hND
  set N0 := normalizedLayered LG s.data s.plain s.decodes s.placement.lower s.exceptional p with hN0
  have hdN0 : ND.Decodes s.plain N0.garden := normalized_decodes LG s.data s.plain s.decodes _ _ p
  have hnil : ND.tree s.placement.lower = .nil := baseData_tree_lower s false
  have hq : ND.couple (pairOfLeaf s.skeleton s.plain s.placement.retained) = .triv :=
    (s.data.eraseTree s.placement.lower).eraseCouple_at _
  have he : SameLowerLayer N0 (expandedPlacement ND s.plain hdN0 s.placement hq) :=
    normalization_sameLower LG s.data s.plain s.decodes s.placement s.canonical s.treeCoherent
        s.coupleCoherent s.core s.selected s.eligible
  have hbase : s.base true = unitLayerTwist N0 (expandedPlacement ND s.plain hdN0 s.placement hq) he := rfl
  have hbd : s.baseData true = twistReconstruction s.skeleton s.placement s.plain ND := rfl
  have hgN : N0.garden = ND.garden s.plain :=
    rawOfGarden_injective_plain hdN0.1 (ND.garden_plain _) (hdN0.2.symm.trans (ND.garden_raw _).symm)
  have heu := fun z hz => eu_layer s.placement s.plain ND hnil N0 hdN0 hq he z hz
  refine ⟨?_, ?_, ?_⟩
  · intro b
    rw [hbase]
    refine (hk.1 b).trans ?_
    have hlone : (ND.tree b).lonePath ∈ ((ND.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes :=
      TTree.leaves_subset_nodes _ (chain_lone_mem_leaves (ND.tree b) _)
    have hz : (ND.corePosition b).2 ∈ (N0.garden.tree (ND.corePosition b).1).nodes := by
      rw [hgN]
      exact chain_node_mem_forest ND s.plain b _ hlone
    have hcore : (twistReconstruction s.skeleton s.placement s.plain ND).corePosition
        (coreBranchEquiv s.skeleton s.placement b) =
        inflatedExchange s.skeleton s.placement ND (ND.corePosition b) := by
      unfold ReconstructionData.corePosition
      have ht : (twistReconstruction s.skeleton s.placement s.plain ND).tree
          (coreBranchEquiv s.skeleton s.placement b) = ND.tree b :=
        transportReconstruction_tree _ _ _ _ _ _ b
      rw [ht]
      by_cases hb : b = s.placement.lower
      · subst hb
        rw [hnil]
        simp only [RegChain.lonePath, addrExt_nil]
        exact inflatedPosition_branch_twist s.skeleton s.placement s.plain ND hnil s.placement.lower
      · exact ordinary_chain_node_address_twist s.skeleton ND s.placement s.plain hnil b hb _ hlone
    have := (heu _ hz).symm
    rw [← hcore] at this
    exact this
  · intro b hb q hq'
    rw [hbase]
    refine (hk.2.1 b hb q hq').trans ?_
    have hNDb : ND.tree b = s.data.tree b := s.data.eraseTree_other _ _ hb
    have hmem : q ∈ ((ND.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes := by rw [hNDb]; exact hq'
    have hz : (addrExt (inflatedPosition s.skeleton ND.tree b.toNode) q).2 ∈
        (N0.garden.tree (addrExt (inflatedPosition s.skeleton ND.tree b.toNode) q).1).nodes := by
      rw [hgN]
      exact chain_node_mem_forest ND s.plain b q hmem
    have hpos := ordinary_chain_node_address_twist s.skeleton ND s.placement s.plain hnil b hb q hmem
    have := (heu _ hz).symm
    rw [← hpos] at this
    exact this
  · intro q hq' i r hr
    rw [hbase]
    refine (hk.2.2 q hq' i r).trans ?_
    have hne : q ≠ pairOfLeaf s.skeleton s.plain s.placement.retained := hq'
    have hsides := twistSourcePair_sides s.skeleton s.placement s.plain q hne
    have hlne := pair_leaves_ne (S := s.skeleton) s.plain hq'
    -- the leaf at side `i`
    have key : ∀ (l : GLeaf s.skeleton.tree), l ≠ s.skeleton.pair s.placement.retained →
        r ∈ (ND.leafTree s.plain l).nodes →
        layerAt N0 (addrExt (inflatedPosition s.skeleton ND.tree l.toNode) r) =
          layerAt (unitLayerTwist N0 (expandedPlacement ND s.plain hdN0 s.placement hq) he)
            (addrExt (inflatedPosition (unitTwistGarden s.skeleton s.placement)
              (twistReconstruction s.skeleton s.placement s.plain ND).tree (coreLeafEquiv s.skeleton s.placement l).toNode) r) := by
      intro l hl hrl
      have hz : (addrExt (inflatedPosition s.skeleton ND.tree l.toNode) r).2 ∈
          (N0.garden.tree (addrExt (inflatedPosition s.skeleton ND.tree l.toNode) r).1).nodes := by
        rw [hgN]
        have hs := (ND.forest_subtree_position s.plain l.toNode).trans
          (congrArg some (ND.inflateNode_leaf s.plain l))
        exact (Comb.subtree_nodes_iff hs r).mp hrl
      have hv := congrArg (fun a => addrExt a r) (inflatedPosition_leaf_twist s.skeleton s.placement s.plain ND hnil l)
      have heq := (inflatedExchange_leaf_respectsAt s.skeleton s.placement ND l hl) r
      exact (heu _ hz).symm.trans (congrArg _ (heq.trans hv.symm))
    have hnp : ∀ l : GLeaf s.skeleton.tree, pairOfLeaf s.skeleton s.plain l = q →
        l ≠ s.skeleton.pair s.placement.retained := by
      intro l hl he
      apply hq'
      rw [← hl, he, pairOfLeaf_partner]
      rfl
    have hpq : s.pairs true q = twistSourcePairEquiv s.skeleton s.placement s.plain q := rfl
    have hNDq : ND.couple q = s.data.couple q := (s.data.eraseTree s.placement.lower).eraseCouple_other _ _ hq'
    fin_cases i
    · have h1 : coupleRoot ND s.plain q 0 = inflatedPosition s.skeleton ND.tree (q.firstLeaf s.plain).toNode := by
        simp [coupleRoot]
      have h2 : coupleRoot (s.baseData true) (s.chosen_plain true) (s.pairs true q) 0 =
          inflatedPosition (unitTwistGarden s.skeleton s.placement)
            (twistReconstruction s.skeleton s.placement s.plain ND).tree
            (coreLeafEquiv s.skeleton s.placement (q.firstLeaf s.plain)).toNode := by
        have e : (s.pairs true q).firstLeaf (s.chosen_plain true) =
            coreLeafEquiv s.skeleton s.placement (q.firstLeaf s.plain) := hsides.1
        have e0 : coupleRoot (s.baseData true) (s.chosen_plain true) (s.pairs true q) 0 =
            inflatedPosition (s.chosen true) (s.baseData true).tree
              ((s.pairs true q).firstLeaf (s.chosen_plain true)).toNode := by
          simp [coupleRoot]
        rw [e0]
        exact congrArg (fun l => inflatedPosition (unitTwistGarden s.skeleton s.placement)
          (twistReconstruction s.skeleton s.placement s.plain ND).tree l.toNode) e
      have hr' : r ∈ (ND.leafTree s.plain (q.firstLeaf s.plain)).nodes := by
        rw [ND.leafTree_first, hNDq]
        exact hr
      change layerAt N0 (addrExt (coupleRoot ND s.plain q 0) r) =
        layerAt (unitLayerTwist N0 (expandedPlacement ND s.plain hdN0 s.placement hq) he)
          (addrExt (coupleRoot (s.baseData true) (s.chosen_plain true) (s.pairs true q) 0) r)
      rw [h1, h2]
      exact key _ (hnp _ (pairOfLeaf_firstLeaf _ _ q)) hr'
    · have h1 : coupleRoot ND s.plain q 1 = inflatedPosition s.skeleton ND.tree (q.secondLeaf s.plain).toNode := by
        simp [coupleRoot]
      have h2 : coupleRoot (s.baseData true) (s.chosen_plain true) (s.pairs true q) 1 =
          inflatedPosition (unitTwistGarden s.skeleton s.placement)
            (twistReconstruction s.skeleton s.placement s.plain ND).tree
            (coreLeafEquiv s.skeleton s.placement (q.secondLeaf s.plain)).toNode := by
        have e : (s.pairs true q).secondLeaf (s.chosen_plain true) =
            coreLeafEquiv s.skeleton s.placement (q.secondLeaf s.plain) := hsides.2
        have e0 : coupleRoot (s.baseData true) (s.chosen_plain true) (s.pairs true q) 1 =
            inflatedPosition (s.chosen true) (s.baseData true).tree
              ((s.pairs true q).secondLeaf (s.chosen_plain true)).toNode := by
          simp [coupleRoot]
        rw [e0]
        exact congrArg (fun l => inflatedPosition (unitTwistGarden s.skeleton s.placement)
          (twistReconstruction s.skeleton s.placement s.plain ND).tree l.toNode) e
      have hr' : r ∈ (ND.leafTree s.plain (q.secondLeaf s.plain)).nodes := by
        rw [ND.leafTree_second, hNDq]
        exact hr
      change layerAt N0 (addrExt (coupleRoot ND s.plain q 1) r) =
        layerAt (unitLayerTwist N0 (expandedPlacement ND s.plain hdN0 s.placement hq) he)
          (addrExt (coupleRoot (s.baseData true) (s.chosen_plain true) (s.pairs true q) 1) r)
      rw [h1, h2]
      exact key _ (hnp _ (pairOfLeaf_secondLeaf _ _ q)) hr'

theorem k2_pins (s : LFSource p kind LG) (ε : Bool) : K2Pins s ε := by
  cases ε
  · exact k2_false s
  · exact k2_true s

theorem hplug_of (s : LFSource p kind LG) (ε : Bool) :
    ∀ b : GBranch s.skeleton.tree, b ≠ s.placement.lower →
      ∀ q ∈ ((s.data.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes,
        q ∈ (((s.baseData ε).tree (s.branches ε b)).plug (nodeSign (s.chosen ε).sig (s.branches ε b).1) .leaf).nodes := by
  intro b hb q hq
  rw [s.base_tree_other ε b hb]
  cases ε
  · exact hq
  · have hs := coreBranchEquiv_sign s.skeleton s.placement b
    rw [if_neg hb] at hs
    change nodeSign (unitTwistGarden s.skeleton s.placement).sig (coreBranchEquiv s.skeleton s.placement b).1 =
      nodeSign s.skeleton.sig b.1 at hs
    change q ∈ ((s.data.tree b).plug (nodeSign (unitTwistGarden s.skeleton s.placement).sig
      (coreBranchEquiv s.skeleton s.placement b).1) .leaf).nodes
    rw [hs]
    exact hq

end WaveTurbulence.Stage1
