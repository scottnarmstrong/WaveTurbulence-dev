/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CollapseLayers
public import WaveTurbulence.Foundations.Molecule.LFTwist.CollapseAddresses

/-! # Literal outside agreement for layered paired-tree collapse -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ} (LG : LayeredGarden w) {a b : GNode LG.garden.tree}
    (h : Comb.IsSubPairedTree LG.garden a b)

private theorem outside_interval_raw (z : Address w) (hz : ¬ InTree a.1 b.1 z) :
    ¬ Below a.1 z ∨ Below b.1 z := by
  by_cases ha : Below a.1 z
  · right
    by_contra hb
    exact hz ⟨(under_iff_below_addr a.1 z).mpr ha,
      fun ht => hb ((under_iff_below_addr b.1 z).mp ht)⟩
  · exact Or.inl ha

private theorem tree_stretch_shift (z : Address w) (hz : ¬ InTree a.1 b.1 z) :
    stretch a.1 (Comb.collapseDataOfDesc h.1).path (shiftAddr b.1 a.1 z) = z := by
  have hp := collapseData_frame h.1
  rw [hp] at hz ⊢
  exact stretch_shift_collapse a.1 z _ hz

/-- Exact old/new leaf membership under the source lone-root move. -/
theorem treeCollapse_leaf_outside (z : Address w) (hz : ¬ InTree a.1 b.1 z) :
    z.2 ∈ (LG.garden.tree z.1).leaves ↔
      (shiftAddr b.1 a.1 z).2 ∈ ((collapsePairedTreeGarden h).tree (shiftAddr b.1 a.1 z).1).leaves := by
  constructor
  · intro hl
    obtain ⟨x,hx⟩ := (replacement_leaf_image LG.garden.tree a b _ (collapseData_frame h.1)
      ⟨z,hl⟩).mp (outside_interval_raw LG z hz)
    have he : x.1 = shiftAddr b.1 a.1 z :=
      stretch_injective a.1 _ (hx.trans (tree_stretch_shift LG h z hz).symm)
    exact he ▸ x.2
  · intro hl
    have hs := replacement_stretch_leaf LG.garden.tree a b _ (collapseData_frame h.1)
      (shiftAddr b.1 a.1 z) hl
    rwa [tree_stretch_shift LG h z hz] at hs

/-- Exact old/new branching membership under the same move. -/
theorem treeCollapse_branch_outside (z : Address w) (hz : ¬ InTree a.1 b.1 z) :
    z.2 ∈ (LG.garden.tree z.1).branching ↔
      (shiftAddr b.1 a.1 z).2 ∈ ((collapsePairedTreeGarden h).tree (shiftAddr b.1 a.1 z).1).branching := by
  constructor
  · intro hl
    obtain ⟨x,hx⟩ := (replacement_branch_image LG.garden.tree a b _ (collapseData_frame h.1)
      ⟨z,hl⟩).mp (outside_interval_raw LG z hz)
    have he : x.1 = shiftAddr b.1 a.1 z :=
      stretch_injective a.1 _ (hx.trans (tree_stretch_shift LG h z hz).symm)
    exact he ▸ x.2
  · intro hl
    have hs := replacement_stretch_branch LG.garden.tree a b _ (collapseData_frame h.1)
      (shiftAddr b.1 a.1 z) hl
    rwa [tree_stretch_shift LG h z hz] at hs

theorem treeCollapse_node_outside (z : Address w) (hz : ¬ InTree a.1 b.1 z) :
    z.2 ∈ (LG.garden.tree z.1).nodes ↔
      (shiftAddr b.1 a.1 z).2 ∈ ((collapsePairedTreeGarden h).tree (shiftAddr b.1 a.1 z).1).nodes := by
  rw [TTree.mem_nodes_iff, TTree.mem_nodes_iff,
    treeCollapse_leaf_outside LG h z hz, treeCollapse_branch_outside LG h z hz]

/-- The actual prefix-pullback layering satisfies all four C4 outside-agreement fields. -/
theorem collapsePairedTree_outAgree :
    OutAgreeT LG (collapsePairedTreeLayered LG h) a.1 b.1 a.1 := by
  constructor
  · exact treeCollapse_node_outside LG h
  · exact treeCollapse_leaf_outside LG h
  · intro z hz
    by_cases hn : z.2 ∈ (LG.garden.tree z.1).nodes
    · have hm := (treeCollapse_node_outside LG h z hz).mp hn
      rw [layerAt_of_mem LG hn, layerAt_of_mem (collapsePairedTreeLayered LG h) hm]
      change LG.layer ⟨z,hn⟩ = LG.layer (collapsePairedTreeNodeEmbedding h ⟨shiftAddr b.1 a.1 z,hm⟩)
      apply congrArg LG.layer
      exact Subtype.ext (tree_stretch_shift LG h z hz).symm
    · have hm := mt (treeCollapse_node_outside LG h z hz).mpr hn
      have hm' : (shiftAddr b.1 a.1 z).2 ∉
          ((collapsePairedTreeLayered LG h).garden.tree (shiftAddr b.1 a.1 z).1).nodes := hm
      unfold layerAt
      rw [dite_eq_right hn, dite_eq_right hm']
  · intro l m hz he
    have hm : pairedTreeLeafEmbedding h m = l := by
      apply Subtype.ext
      change stretch a.1 _ m.1 = l.1
      rw [← he]
      exact tree_stretch_shift LG h l.1 hz
    have hp := collapsePairedTreeGarden_pair h m
    rw [hm] at hp
    have hv := congrArg (fun l : GLeaf LG.garden.tree => shiftAddr b.1 a.1 l.1) hp
    change shiftAddr b.1 a.1 (stretch a.1 _ ((collapsePairedTreeGarden h).pair m).1) =
      shiftAddr b.1 a.1 (LG.garden.pair l).1 at hv
    rw [collapseData_frame h.1, shift_stretch_collapse] at hv
    have hv' : shiftAddr b.1 a.1 (LG.garden.pair l).1 =
        ((collapsePairedTreeGarden h).pair m).1 := by
      simpa only [← collapseData_frame h.1] using hv.symm
    exact hv'

end WaveTurbulence.LFTwist
