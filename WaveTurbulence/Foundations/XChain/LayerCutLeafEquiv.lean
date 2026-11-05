/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutAttachments
/-! The inverse top-leaf carrier splits into source attachment roots and terminal top-layer leaves. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

noncomputable def classifyLayerCutLeaf {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (a : GLeaf (layerCutForest LG p)) :
    ↥(LG.attachNodes p) ⊕ {ℓ : GLeaf LG.garden.tree // LG.layer ℓ.toNode = p} :=
  if hlo : LG.layer (layerCutNodeEmbedding LG p a.toNode) < p then
    .inl ⟨layerCutNodeEmbedding LG p a.toNode,
      Finset.mem_filter.mpr ⟨mem_univ _, hlo, layerCut_leaf_parentLayer LG p hbound a⟩⟩
  else
    .inr ⟨⟨a.1, (layerCut_leaf_original_or_lower LG p a).resolve_right hlo⟩,
      le_antisymm (hbound _) (Nat.le_of_not_gt hlo)⟩

noncomputable def layerCutLeafEquiv {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) :
    GLeaf (layerCutForest LG p) ≃
      ↥(LG.attachNodes p) ⊕ {ℓ : GLeaf LG.garden.tree // LG.layer ℓ.toNode = p} where
  toFun := classifyLayerCutLeaf LG p hbound
  invFun := Sum.elim (attachNodeToCutLeaf LG p) (fun ℓ => topLayerLeafToCut LG p ℓ.1 ℓ.2.ge)
  left_inv a := by
    unfold classifyLayerCutLeaf
    split_ifs <;> apply Subtype.ext <;> rfl
  right_inv z := by
    rcases z with a | ℓ
    · have hlo : LG.layer (layerCutNodeEmbedding LG p (attachNodeToCutLeaf LG p a).toNode) < p :=
        (Finset.mem_filter.mp a.2).2.1
      change classifyLayerCutLeaf LG p hbound (attachNodeToCutLeaf LG p a) = .inl a
      rw [classifyLayerCutLeaf, dite_eq_left hlo]
      apply congrArg Sum.inl
      apply Subtype.ext
      rfl
    · have hn : ¬ LG.layer (layerCutNodeEmbedding LG p (topLayerLeafToCut LG p ℓ.1 ℓ.2.ge).toNode) < p :=
        Nat.not_lt.mpr ℓ.2.ge
      change classifyLayerCutLeaf LG p hbound (topLayerLeafToCut LG p ℓ.1 ℓ.2.ge) = .inr ℓ
      rw [classifyLayerCutLeaf, dite_eq_right hn]
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Subtype.ext
      rfl

end WaveTurbulence.Induct
