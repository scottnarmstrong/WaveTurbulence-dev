/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepBr5
public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionEmbeddings
public import WaveTurbulence.Foundations.Spine.CoherentObjects
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSigns
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairSides
import Mathlib.Tactic

/-!
# S2 REPRESENTS: a coherent native couple is an embedded coherent couple (`IsCoherentCoupleAt`)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed
  WaveTurbulence.LFTwist WaveTurbulence.Links

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem couple_coherent_at (p : ℕ) (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer))
    (p' : SourcePair S)
    (hg : (nativeCoupleLayered D hS layer hLayer p').incoherency (D.couple p').links = 0) :
    IsCoherentCoupleAt p
      (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inl p') 0))
      (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inl p') 1))
      (D.couple p') (nativeCoupleLayered D hS layer hLayer p') := by
  have hQ := couple_decodes D hS layer hLayer p'
  have hE := reconstruction_coupleEmb D hS (D.garden_decodes hS) p'
  refine ⟨D.couple_wf p', hQ, w, layeredReconstruction D hS layer hLayer,
    inflatedPosition S D.tree (p'.firstLeaf hS).toNode, inflatedPosition S D.tree (p'.secondLeaf hS).toNode,
    hcan, hE, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show nodeSign S.sig _ = 1
    rw [inflatedPosition_sign]
    exact sourcePair_first_sign S hS p'
  · show nodeSign S.sig _ = -1
    rw [inflatedPosition_sign]
    exact sourcePair_second_sign S hS p'
  · intro l hl
    rw [coupleLinksAt_eq_map] at hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    have hbr := link_branching hQ hl0
    have e1 := couple_layerAt_of_mem D hS layer hLayer p' l0.1 (TTree.branching_subset_nodes _ hbr.1)
    have e2 := couple_layerAt_of_mem D hS layer hLayer p' l0.2 (TTree.branching_subset_nodes _ hbr.2.1)
    show layerAt _ (coupleAddr D hS p' l0.1) = layerAt _ (coupleAddr D hS p' l0.2)
    rw [e1, e2]
    exact (coherent_iff hQ).1 hg l0 hl0
  · have hmem := hE.nodeA
    have h1 := parAt_of_mem (layeredReconstruction D hS layer hLayer) p hmem
    rw [h1]
    have hcl : argSrc hS (.inl p') 0 = clkOfNode S (p'.firstLeaf hS).toNode := by simp [argSrc]
    rw [hcl]
    exact parentLayer_inflated D hS layer hLayer p _ ⟨_, hmem⟩ rfl
  · have hmem := hE.nodeB
    have h1 := parAt_of_mem (layeredReconstruction D hS layer hLayer) p hmem
    rw [h1]
    have hcl : argSrc hS (.inl p') 1 = clkOfNode S (p'.secondLeaf hS).toNode := by simp [argSrc]
    rw [hcl]
    exact parentLayer_inflated D hS layer hLayer p _ ⟨_, hmem⟩ rfl
  · intro z
    have key : ∀ x : Fin 2 × TTree.Path, coupleAddr D hS p' x =
        addrExt (if x.1 = 0 then inflatedPosition S D.tree (p'.firstLeaf hS).toNode
          else inflatedPosition S D.tree (p'.secondLeaf hS).toNode) x.2 := by
      rintro ⟨j, path⟩
      fin_cases j <;> rfl
    have h1 := couple_layerAt D hS layer hLayer p' z
    rw [key] at h1
    exact h1.symm

end WaveTurbulence.Represents
