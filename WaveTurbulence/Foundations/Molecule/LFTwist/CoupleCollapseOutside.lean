/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CollapseLayers

/-! # Literal outside data of the actual couple collapse -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton
variable {w : ℕ} (LG : LayeredGarden w) {a b : GNode LG.garden.tree}
    (h : Comb.IsSubCouple LG.garden a b)

theorem coupleCollapse_leaf_outside (z : Address w)
    (ha : ¬ Below a.1 z) (hb : ¬ Below b.1 z) :
    z.2 ∈ ((collapseCoupleGarden h).tree z.1).leaves ↔
      z.2 ∈ (LG.garden.tree z.1).leaves := by
  change z.2 ∈ (collapsePairForest LG.garden.tree a b (Comb.subCouple_incomparable h) z.1).leaves ↔ _
  rw [collapsePairForest_leaf_iff]
  constructor
  · rintro (⟨hl,_,_⟩ | he | he)
    · exact hl
    · exact (ha (he ▸ ⟨rfl,List.prefix_refl _⟩)).elim
    · exact (hb (he ▸ ⟨rfl,List.prefix_refl _⟩)).elim
  · exact fun hl => Or.inl ⟨hl,ha,hb⟩

theorem coupleCollapse_branch_outside (z : Address w)
    (ha : ¬ Below a.1 z) (hb : ¬ Below b.1 z) :
    z.2 ∈ ((collapseCoupleGarden h).tree z.1).branching ↔
      z.2 ∈ (LG.garden.tree z.1).branching := by
  change z.2 ∈ (collapsePairForest LG.garden.tree a b (Comb.subCouple_incomparable h) z.1).branching ↔ _
  rw [collapsePairForest_branch_iff]
  exact ⟨fun ht => ht.1, fun ht => ⟨ht,ha,hb⟩⟩

theorem coupleCollapse_node_outside (z : Address w)
    (ha : ¬ Below a.1 z) (hb : ¬ Below b.1 z) :
    z.2 ∈ ((collapseCoupleGarden h).tree z.1).nodes ↔
      z.2 ∈ (LG.garden.tree z.1).nodes := by
  rw [TTree.mem_nodes_iff, TTree.mem_nodes_iff,
    coupleCollapse_leaf_outside LG h z ha hb, coupleCollapse_branch_outside LG h z ha hb]

/-- The surviving pair retains both literal original leaf addresses. -/
theorem coupleCollapse_pair_outside (l : GLeaf LG.garden.tree)
    (m : GLeaf (collapseCoupleGarden h).tree)
    (ha : ¬ Below a.1 l.1) (hb : ¬ Below b.1 l.1) (he : l.1 = m.1) :
    (LG.garden.pair l).1 = ((collapseCoupleGarden h).pair m).1 := by
  let x : OutsideRoots LG.garden.tree a b := ⟨l,ha,hb⟩
  have hm : collapseLeafEquiv LG.garden.tree a b (Comb.subCouple_incomparable h) (.inl x) = m :=
    Subtype.ext he
  have hp := collapseCoupleGarden_pair_old h x
  rw [hm] at hp
  exact (congrArg (fun n : GLeaf (collapseCoupleGarden h).tree => n.1) hp).symm

/-- Every surviving parent is an old branch at the same address and layer. -/
theorem coupleCollapse_parentLayer (p : ℕ) (n : GNode LG.garden.tree)
    (m : GNode (collapseCoupleGarden h).tree) (he : n.1 = m.1) :
    LG.parentLayer p n = (collapseCoupleLayered LG h p).parentLayer p m := by
  by_cases hn : n.1.2 = []
  · have hm : m.1.2 = [] := (congrArg Prod.snd he).symm.trans hn
    simp only [LayeredGarden.parentLayer, hn, hm, ite_true]
  · have hm : m.1.2 ≠ [] := fun hz => hn ((congrArg Prod.snd he).trans hz)
    rw [parentLayer_nonroot LG p n hn,
      parentLayer_nonroot (collapseCoupleLayered LG h p) p m hm]
    have he' : (GNode.parent n hn).toNode =
        (collapseCoupleBranchEmbedding h (GNode.parent m hm)).toNode := by
      apply congrArg GBranch.toNode
      exact Subtype.ext (congrArg (fun z : Address w => (z.1,z.2.dropLast)) he)
    exact (congrArg LG.layer he').trans (collapseCoupleLayered_branch LG h p (GNode.parent m hm)).symm

/-- Outside leaves inherit their exact old layers when the source is canonical. -/
theorem coupleCollapse_leaf_layer (p : ℕ) (hc : LG.CanonCriterion p)
    (hplain : LG.garden.IsPlain) (l : GLeaf LG.garden.tree)
    (m : GLeaf (collapseCoupleGarden h).tree)
    (ha : ¬ Below a.1 l.1) (hb : ¬ Below b.1 l.1) (he : l.1 = m.1) :
    LG.layer l.toNode = (collapseCoupleLayered LG h p).layer m.toNode := by
  have hf : (collapseCoupleLayered LG h p).layer m.toNode =
      min ((collapseCoupleLayered LG h p).parentLayer p m.toNode)
        ((collapseCoupleLayered LG h p).parentLayer p ((collapseCoupleGarden h).pair m).toNode) := by
    exact (extendBranchLayers_leaf _ _ p m).trans (congrArg₂ min
      (branchParentValue_eq_extension_parentLayer _ _ p (collapseCouple_branchPrelayering LG h) m.toNode)
      (branchParentValue_eq_extension_parentLayer _ _ p (collapseCouple_branchPrelayering LG h)
        ((collapseCoupleGarden h).pair m).toNode))
  have hp := coupleCollapse_pair_outside LG h l m ha hb he
  exact (canonical_leaf_layer LG hc hplain l).trans ((congrArg₂ min
    (coupleCollapse_parentLayer LG h p l.toNode m.toNode he)
    (coupleCollapse_parentLayer LG h p (LG.garden.pair l).toNode
      ((collapseCoupleGarden h).pair m).toNode hp)).trans hf.symm)

end WaveTurbulence.LFTwist
