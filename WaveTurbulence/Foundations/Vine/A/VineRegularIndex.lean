/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineIngredientSum
public import WaveTurbulence.Foundations.Vine.A.VineRowCounts
/-! Regular-row incoherency transport for actual LF constructions. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open TTree Reg Reg.Skeleton LFTwist Links RegRed

/-- A coherent link list has zero incoherency, without any regularity assumption. -/
theorem incoherency_eq_zero_of_cohOn {w : ℕ} (LG : LayeredGarden w) (ls : List (Pair w))
    (h : CohOn LG ls) : LG.incoherency ls = 0 := by
  classical
  unfold LayeredGarden.incoherency
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro bb hb
  have hh := (Finset.mem_filter.mp hb).2
  have he := h (bb.1.1, bb.2.1) hh.1
  change layerAt LG bb.1.toNode.1 = layerAt LG bb.2.toNode.1 at he
  rw [layerAt_node LG bb.1.toNode, layerAt_node LG bb.2.toNode] at he
  exact hh.2 he

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}

/-- Every ordinary tree row has exactly its original incoherency index. -/
theorem lf_tree_index_other (C : LFConstruction s ε) (b : GBranch s.skeleton.tree)
    (hb : b ≠ s.placement.lower) :
    C.output.incoherency ((C.data.tree (s.branches ε b)).linksAt
      (nodeSign (s.chosen ε).sig (s.branches ε b).1)
      (inflatedPosition (s.chosen ε) C.data.tree (s.branches ε b).toNode)) =
    LG.incoherency ((s.data.tree b).linksAt (nodeSign s.skeleton.sig b.1)
      (inflatedPosition s.skeleton s.data.tree b.toNode)) := by
  classical
  rw [decoded_tree_incoherency_count C.data (s.chosen_plain ε) C.output C.decodes,
    decoded_tree_incoherency_count s.data s.plain LG s.decodes,
    C.tree_other b hb, s.ordinary_branch_sign ε b hb]
  apply congrArg List.length
  apply List.filter_congr
  intro l hl
  have hd := decodedTree_decodes (s.data.tree b) (nodeSign s.skeleton.sig b.1)
  have h0 := (tree_mem_pairEndpoints_links_iff hd l.1).mp
    ((mem_pairEndpoints_iff _ _).mpr ⟨l, hl, Or.inl rfl⟩)
  have h1 := (tree_mem_pairEndpoints_links_iff hd l.2).mp
    ((mem_pairEndpoints_iff _ _).mpr ⟨l, hl, Or.inr rfl⟩)
  have e0 := C.ordinaryTreeLayers b hb l.1.2 (TTree.branching_subset_nodes _ h0)
  have e1 := C.ordinaryTreeLayers b hb l.2.2 (TTree.branching_subset_nodes _ h1)
  change layerAt LG (chainAddr s.data b l.1) =
    layerAt C.output (chainAddr C.data (s.branches ε b) l.1) at e0
  change layerAt LG (chainAddr s.data b l.2) =
    layerAt C.output (chainAddr C.data (s.branches ε b) l.2) at e1
  rw [← e0, ← e1]

/-- Every ordinary couple row has exactly its original incoherency index. -/
theorem lf_couple_index_other (C : LFConstruction s ε) (q : SourcePair s.skeleton)
    (hq : q ≠ s.exceptional) :
    C.output.incoherency ((C.data.couple (s.pairs ε q)).linksAt
      (inflatedPosition (s.chosen ε) C.data.tree ((s.pairs ε q).firstLeaf (s.chosen_plain ε)).toNode)
      (inflatedPosition (s.chosen ε) C.data.tree ((s.pairs ε q).secondLeaf (s.chosen_plain ε)).toNode)) =
    LG.incoherency ((s.data.couple q).linksAt
      (inflatedPosition s.skeleton s.data.tree (q.firstLeaf s.plain).toNode)
      (inflatedPosition s.skeleton s.data.tree (q.secondLeaf s.plain).toNode)) := by
  classical
  rw [decoded_couple_incoherency_count C.data (s.chosen_plain ε) C.output C.decodes,
    decoded_couple_incoherency_count s.data s.plain LG s.decodes, C.couple_other q hq]
  apply congrArg List.length
  apply List.filter_congr
  intro l hl
  have hbr := link_branching (decodedCouple_decodes (s.data.couple q)) hl
  have e0 := C.ordinaryCoupleLayers q hq l.1.1 l.1.2 (TTree.branching_subset_nodes _ hbr.1)
  have e1 := C.ordinaryCoupleLayers q hq l.2.1 l.2.2 (TTree.branching_subset_nodes _ hbr.2.1)
  change layerAt LG (addrExt (coupleRoot s.data s.plain q l.1.1) l.1.2) =
    layerAt C.output (addrExt (coupleRoot C.data (s.chosen_plain ε) (s.pairs ε q) l.1.1) l.1.2) at e0
  change layerAt LG (addrExt (coupleRoot s.data s.plain q l.2.1) l.2.2) =
    layerAt C.output (addrExt (coupleRoot C.data (s.chosen_plain ε) (s.pairs ε q) l.2.1) l.2.2) at e1
  simp only [coupleAddr_eq_root]
  rw [← e0, ← e1]

end WaveTurbulence.VineA
