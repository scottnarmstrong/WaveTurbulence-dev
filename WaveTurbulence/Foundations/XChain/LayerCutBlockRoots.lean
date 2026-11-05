/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutLeafEquiv
public import WaveTurbulence.Foundations.XChain.ExtractedSubforest
/-! Original root sets corresponding to blocks of inverse top leaves. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def cutLeafNodeEmbedding {w : ℕ} (LG : LayeredGarden w) (p : ℕ) :
    GLeaf (layerCutForest LG p) ↪ GNode LG.garden.tree where
  toFun a := layerCutNodeEmbedding LG p a.toNode
  inj' a b he := by
    apply Subtype.ext
    exact congrArg (fun u : GNode LG.garden.tree => u.1) he

noncomputable def cutBlockRoots {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p))) : Finset (GNode LG.garden.tree) :=
  B.map (cutLeafNodeEmbedding LG p)

theorem cutBlockRoots_antichain {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p))) : Canon.Rel.Antichain LG (cutBlockRoots LG p B) := by
  intro u hu v hv hne
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
  constructor
  · intro h
    have he : a = b := GLeaf.eq_of_isDesc h
    exact hne (congrArg (cutLeafNodeEmbedding LG p) he)
  · intro h
    have he : b = a := GLeaf.eq_of_isDesc h
    exact hne (congrArg (cutLeafNodeEmbedding LG p) he.symm)

noncomputable def cutBlockRootEquiv {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p))) : ↥B ≃ ↥(cutBlockRoots LG p B) :=
  Equiv.ofBijective (fun a => ⟨cutLeafNodeEmbedding LG p a.1, Finset.mem_map.mpr ⟨a.1, a.2, rfl⟩⟩) (by
    constructor
    · intro a b he
      apply Subtype.ext
      exact (cutLeafNodeEmbedding LG p).injective (congrArg Subtype.val he)
    · rintro ⟨u, hu⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
      exact ⟨⟨a, ha⟩, rfl⟩)

noncomputable def cutBlockRootIndexEquiv {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p))) : Fin B.card ≃ Fin (cutBlockRoots LG p B).card :=
  B.equivFin.symm.trans ((cutBlockRootEquiv LG p B).trans (cutBlockRoots LG p B).equivFin)

theorem cutBlockRootIndexEquiv_root {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p))) (k : Fin B.card) :
    subforestRoot (cutBlockRoots LG p B) (cutBlockRootIndexEquiv LG p B k) =
      cutLeafNodeEmbedding LG p (B.equivFin.symm k).1 :=
  subforestRoot_equivFin _ _

end WaveTurbulence.Induct
