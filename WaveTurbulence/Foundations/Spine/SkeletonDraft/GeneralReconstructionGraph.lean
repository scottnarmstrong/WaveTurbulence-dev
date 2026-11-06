/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GeneralReconstructionTrace
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReductionTraceGraph
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.DecodedCoreEmbedding
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestOpenGraph

/-! # Exact labelled core history for every regular reconstruction assignment -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.graph_reduces_core {w : ℕ} {S G : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G) :
    PortMatching.Reduces (ambientWithPadding (v := 2) G).graph
      (LabelledGarden.mk S ((D.decodedCoreEmbedding hS hd).trans Function.Embedding.inl)).graph := by
  classical
  obtain ⟨T,hT⟩ := D.reduction_trace hS G hd
  have he : T.branches = D.decodedCoreEmbedding hS hd := by
    apply Function.Embedding.ext
    intro b
    exact Subtype.ext (hT b)
  have hg := T.graph_reduces (ambientWithPadding (v := 2) G).label
  rw [he] at hg
  exact hg

end WaveTurbulence.Reg.Skeleton
