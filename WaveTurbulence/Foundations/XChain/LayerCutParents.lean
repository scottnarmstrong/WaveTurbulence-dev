/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutForest
public import WaveTurbulence.Foundations.XChain.GraftParents
/-! Every cut leaf has parent layer p, including roots with the source's parent convention. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def nodeParentBranch {w : ℕ} {tree : Fin w → TTree}
    (a : GNode tree) (ha : a.1.2 ≠ []) : GBranch tree :=
  ⟨(a.1.1, a.1.2.dropLast), TTree.branching_of_append_mem _
    ((List.dropLast_append_getLast ha).symm ▸ a.2)⟩

theorem layerCut_leaf_parentLayer {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (a : GLeaf (layerCutForest LG p)) :
    LG.parentLayer p (layerCutNodeEmbedding LG p a.toNode) = p := by
  by_cases ha : a.1.2 = []
  · have he : (layerCutNodeEmbedding LG p a.toNode).1.2 = [] := ha
    simp only [LayeredGarden.parentLayer, he, ite_true]
  · have he := parentLayer_eq_layer_par LG p (layerCutNodeEmbedding LG p a.toNode) ha
    have hp := layerCut_branch_layer LG p hbound (nodeParentBranch a.toNode ha)
    exact he.trans hp

theorem layerCut_leaf_attach_or_terminal {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (a : GLeaf (layerCutForest LG p)) :
    layerCutNodeEmbedding LG p a.toNode ∈ LG.attachNodes p ∨
      a.1.2 ∈ (LG.garden.tree a.1.1).leaves ∧ LG.layer (layerCutNodeEmbedding LG p a.toNode) = p := by
  classical
  by_cases ha : LG.layer (layerCutNodeEmbedding LG p a.toNode) < p
  · exact Or.inl (Finset.mem_filter.mpr ⟨mem_univ _, ha, layerCut_leaf_parentLayer LG p hbound a⟩)
  · have hleaf := (layerCut_leaf_original_or_lower LG p a).resolve_right ha
    exact Or.inr ⟨hleaf, le_antisymm (hbound _) (Nat.le_of_not_gt ha)⟩

end WaveTurbulence.Induct
