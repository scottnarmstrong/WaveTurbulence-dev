/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestOpenPortInjection

/-! # Exact matching compatibility of the actual open subforest port injection -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

noncomputable def selfLabelled {v : ℕ} (H : Garden v) : LabelledGarden v (GBranch H.tree) :=
  ⟨H,Function.Embedding.refl _⟩

theorem selfLabelled_mate_pad {v : ℕ} (H : Garden v) (p : Port H) :
    (selfLabelled H).graph.mate (padPort H p) = padPort H (portMate H p) := by
  have he (q : Port H) : (selfLabelled H).portEmbedding q = padPort H q := by
    cases q <;> rfl
  exact (congrArg (selfLabelled H).graph.mate (he p).symm).trans
    (((selfLabelled H).graph_mate_embedding p).trans (he (portMate H p)))

theorem ambient_padding_fixed {w v : ℕ} (G : Garden w) (j : Fin v) (i : Fin 4) :
    (ambientWithPadding (v := v) G).graph.mate (.inr (.inr j),i) = (.inr (.inr j),i) := by
  apply extendMate_outside
  rintro ⟨p,hp⟩
  cases p with
  | inl k =>
    have he : (Sum.inl k : Fin w ⊕ (GBranch G.tree ⊕ Fin v)) = .inr (.inr j) :=
      congrArg (fun z : (Fin w ⊕ (GBranch G.tree ⊕ Fin v)) × Fin 4 => z.1) hp
    cases he
  | inr p =>
    have he : (Sum.inr (Sum.inl p.1) : Fin w ⊕ (GBranch G.tree ⊕ Fin v)) = .inr (.inr j) :=
      congrArg (fun z : (Fin w ⊕ (GBranch G.tree ⊕ Fin v)) × Fin 4 => z.1) hp
    cases Sum.inr.inj he

theorem subforestOpenPort_mate {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (p : UniformPort (E.inducedGarden hc)) :
    (ambientWithPadding (v := v) G).graph.mate (subforestOpenPort G E hc p) =
      subforestOpenPort G E hc ((selfLabelled (E.inducedGarden hc)).graph.mate p) := by
  rcases uniformPort_actual_or_dummy (E.inducedGarden hc) p with ⟨q,rfl⟩ | ⟨j,i,hi,rfl⟩
  · rw [subforestOpenPort_pad,selfLabelled_mate_pad,subforestOpenPort_pad]
    exact ((ambientWithPadding (v := v) G).graph_mate_embedding (subforestPortEmbedding G E hc q)).trans
      (congrArg (ambientWithPadding (v := v) G).portEmbedding (subforestPort_mate G E hc q))
  · rw [(selfLabelled (E.inducedGarden hc)).graph_root_inactive j i hi,
      subforestOpenPort_dummy G E hc j i hi,ambient_padding_fixed]

/-- Every original internal branching vertex is mapped with all four ordered ports. -/
theorem subforestOpenPort_branch {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (b : GBranch E.shape) (i : Fin 4) :
    subforestOpenPort G E hc (.inr b,i) = (.inr (.inl (subforestBranchEmbedding E b)),i) := by
  change (ambientWithPadding (v := v) G).portEmbedding (subforestPortEmbedding G E hc (.inr (b,i))) = _
  exact congrArg (ambientWithPadding (v := v) G).portEmbedding (subforestPort_branch G E hc b i)

end WaveTurbulence.Reg.Skeleton
