/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GeneralReconstructionGraph
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionUniqueFixedCore

/-! # DH21 Proposition 4.13: uniqueness of all regular replacements over an actual prime source -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem reconstructionData_unique {w : ℕ} {S G : Garden w}
    (D E : ReconstructionData S) (hS : IsPrimeGarden S)
    (hd : D.Decodes hS.1 G) (he : E.Decodes hS.1 G) : D = E := by
  classical
  let K : LabelledGarden w (GBranch G.tree ⊕ Fin 2) :=
    ⟨S,(D.decodedCoreEmbedding hS.1 hd).trans Function.Embedding.inl⟩
  let L : LabelledGarden w (GBranch G.tree ⊕ Fin 2) :=
    ⟨S,(E.decodedCoreEmbedding hS.1 he).trans Function.Embedding.inl⟩
  have hg : K.graph = L.graph := PortMatching.normal_unique
    (K.graph_normal_of_prime hS) (L.graph_normal_of_prime hS)
    (D.graph_reduces_core hS.1 hd) (E.graph_reduces_core hS.1 he)
  apply reconstructionData_eq_of_fixed_core D E hS.1 hd he
  intro b
  have hl := K.label_eq_of_address L hg b b rfl
  have hb : D.decodedCoreBranch hS.1 hd b = E.decodedCoreBranch hS.1 he b := Sum.inl.inj hl
  exact congrArg (fun c : GBranch G.tree => c.1) hb

end WaveTurbulence.Reg.Skeleton
