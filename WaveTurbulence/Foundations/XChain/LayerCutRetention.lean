/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCutRetention
public import WaveTurbulence.Foundations.XChain.LayerCutParents
/-! Top-layer leaves survive the canonical layer cut, and paired top-layer leaves stay together. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem no_strict_layerCutStop_of_layer_ge {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (a : GNode LG.garden.tree) (hp : p ≤ LG.layer a) :
    ∀ r s, a.1.2 = r ++ s → s ≠ [] → layerCutStop LG p a.1.1 r = false := by
  intro r s hrs _
  have hpre : r <+: a.1.2 := ⟨s, hrs.symm⟩
  let u : GNode LG.garden.tree := ⟨(a.1.1, r), TTree.mem_nodes_of_prefix _ a.2 hpre⟩
  exact (layerCutStop_false_iff LG p u).mpr (hp.trans (LG.layer_le_of_isDesc ⟨rfl, hpre⟩))

theorem layerCut_leaf_mem_of_layer_ge {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (ℓ : GLeaf LG.garden.tree) (hp : p ≤ LG.layer ℓ.toNode) :
    ℓ.1.2 ∈ (layerCutForest LG p ℓ.1.1).leaves :=
  mem_cutTree_leaves_of_no_strict_stop _ _ _ ℓ.2
    (no_strict_layerCutStop_of_layer_ge LG p ℓ.toNode hp)

theorem layerCut_node_mem_of_layer_ge {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (a : GNode LG.garden.tree) (hp : p ≤ LG.layer a) :
    a.1.2 ∈ (layerCutForest LG p a.1.1).nodes :=
  mem_cutTree_nodes_of_no_strict_stop _ _ _ a.2
    (no_strict_layerCutStop_of_layer_ge LG p a hp)

noncomputable def topLayerLeafToCut {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (ℓ : GLeaf LG.garden.tree) (hp : p ≤ LG.layer ℓ.toNode) : GLeaf (layerCutForest LG p) :=
  ⟨ℓ.1, layerCut_leaf_mem_of_layer_ge LG p ℓ hp⟩

theorem layerCut_top_pair_retained {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (ℓ : GLeaf LG.garden.tree) (hp : LG.layer ℓ.toNode = p) :
    (LG.garden.pair ℓ).1.2 ∈ (layerCutForest LG p (LG.garden.pair ℓ).1.1).leaves := by
  have he := LG.isLayering.2 ℓ
  exact layerCut_leaf_mem_of_layer_ge LG p (LG.garden.pair ℓ) (hp.symm.trans he).le

end WaveTurbulence.Induct
