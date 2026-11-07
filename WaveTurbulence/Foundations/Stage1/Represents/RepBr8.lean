/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepBr7
import Mathlib.Tactic

/-!
# S2 REPRESENTS: a coherent native tree is an embedded coherent tree (`IsCoherentTreeAt`)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed
  WaveTurbulence.LFTwist WaveTurbulence.Links

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem tree_coherent_at (p : ℕ) (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer))
    (b : GBranch S.tree)
    (hg : (nativeChainLayered D hS layer hLayer b).incoherency
      ((D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0)) = 0) :
    IsCoherentTreeAt p
      (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr b) 0))
      (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr b) 1))
      (D.tree b) (nativeChainLayered D hS layer hLayer b) := by
  have hX := tree_decodes D hS layer hLayer b
  have hE := reconstruction_chainEmb D hS (D.garden_decodes hS) b
  refine ⟨D.tree_wf b, hX, w, layeredReconstruction D hS layer hLayer,
    inflatedPosition S D.tree b.toNode, _, hcan, hE, ?_, ?_, ?_, ?_, ?_⟩
  · show nodeSign S.sig _ = nodeSign S.sig b.1
    rw [inflatedPosition_sign]
    rfl
  · intro l hl
    have hl' : l ∈ (D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode) := hl
    rw [chainLinksAt_eq_map] at hl'
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl'
    have hbr : l0.1.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree l0.1.1).branching ∧
        l0.2.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree l0.2.1).branching :=
      ⟨(tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l0, hl0, Or.inl rfl⟩),
        (tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l0, hl0, Or.inr rfl⟩)⟩
    have e1 := chain_layerAt_of_mem D hS layer hLayer b l0.1 (TTree.branching_subset_nodes _ hbr.1)
    have e2 := chain_layerAt_of_mem D hS layer hLayer b l0.2 (TTree.branching_subset_nodes _ hbr.2)
    show layerAt _ (chainAddr D b l0.1) = layerAt _ (chainAddr D b l0.2)
    rw [e1, e2]
    exact (tree_coherent_iff hX).1 hg l0 hl0
  · have hmem := hE.node
    have h1 := parAt_of_mem (layeredReconstruction D hS layer hLayer) p hmem
    rw [h1]
    have hcl : argSrc hS (.inr b) 0 = clkOfNode S b.toNode := by simp [argSrc]
    rw [hcl]
    exact parentLayer_inflated D hS layer hLayer p _ ⟨_, hmem⟩ rfl
  · have hcl : argSrc hS (.inr b) 1 = .inr b := by simp [argSrc]
    rw [hcl]
    exact layerAt_node (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b).toNode
  · intro z
    have h1 := chain_layerAt D hS layer hLayer b z
    have key : chainAddr D b z.1 = addrExt (inflatedPosition S D.tree b.toNode) z.1.2 := rfl
    rw [key] at h1
    exact h1.symm

end WaveTurbulence.Represents
