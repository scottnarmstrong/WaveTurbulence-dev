/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCutMembership
public import WaveTurbulence.Foundations.XChain.GraftAddresses
/-! The inverse top forest obtained by cutting at the first node below the top layer. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

noncomputable def layerCutStop {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (j : Fin w) (a : TTree.Path) : Bool :=
  decide (∃ h : a ∈ (LG.garden.tree j).nodes, LG.layer ⟨(j, a), h⟩ < p)

noncomputable def layerCutForest {w : ℕ} (LG : LayeredGarden w) (p : ℕ) : Fin w → TTree :=
  fun j => cutTree (LG.garden.tree j) (layerCutStop LG p j)

theorem layerCutStop_true_iff {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (a : GNode LG.garden.tree) :
    layerCutStop LG p a.1.1 a.1.2 = true ↔ LG.layer a < p := by
  change (decide (∃ h : a.1.2 ∈ (LG.garden.tree a.1.1).nodes,
    LG.layer ⟨a.1, h⟩ < p) = true) ↔ _
  rw [decide_eq_true_eq]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨a.2, h⟩⟩

theorem layerCutStop_false_iff {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (a : GNode LG.garden.tree) :
    layerCutStop LG p a.1.1 a.1.2 = false ↔ p ≤ LG.layer a := by
  constructor
  · intro hs
    apply Nat.le_of_not_gt
    intro h
    have he := hs.symm.trans ((layerCutStop_true_iff LG p a).mpr h)
    cases he
  · intro hp
    apply Bool.eq_false_iff.mpr
    intro hs
    exact (Nat.not_lt.mpr hp) ((layerCutStop_true_iff LG p a).mp hs)

noncomputable def layerCutNodeEmbedding {w : ℕ} (LG : LayeredGarden w) (p : ℕ) :
    GNode (layerCutForest LG p) ↪ GNode LG.garden.tree where
  toFun a := ⟨a.1, cutTree_nodes_subset (LG.garden.tree a.1.1) (layerCutStop LG p a.1.1) a.2⟩
  inj' _ _ h := Subtype.ext (congrArg (fun a : GNode LG.garden.tree => a.1) h)

theorem layerCut_branch_layer {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (b : GBranch (layerCutForest LG p)) :
    LG.layer (layerCutNodeEmbedding LG p b.toNode) = p := by
  have hs := stop_false_of_mem_cutTree_branching (LG.garden.tree b.1.1) (layerCutStop LG p b.1.1) b.2
  exact le_antisymm (hbound _) ((layerCutStop_false_iff LG p
    (layerCutNodeEmbedding LG p b.toNode)).mp hs)

theorem layerCut_leaf_original_or_lower {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (a : GLeaf (layerCutForest LG p)) :
    a.1.2 ∈ (LG.garden.tree a.1.1).leaves ∨ LG.layer (layerCutNodeEmbedding LG p a.toNode) < p := by
  rcases cutTree_leaf_is_original_or_stop (LG.garden.tree a.1.1) (layerCutStop LG p a.1.1) a.2 with h | h
  · exact Or.inl h
  · exact Or.inr ((layerCutStop_true_iff LG p (layerCutNodeEmbedding LG p a.toNode)).mp h)

theorem layerCutForest_graft_reconstruct {w : ℕ} (LG : LayeredGarden w) (p : ℕ) :
    graftForest (layerCutForest LG p) (fun j => subtreeAt (LG.garden.tree j)) = LG.garden.tree := by
  funext j
  exact graftTree_cutTree (LG.garden.tree j) (layerCutStop LG p j)

end WaveTurbulence.Induct
