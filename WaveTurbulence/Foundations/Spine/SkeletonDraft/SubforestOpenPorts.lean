/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestPortSlots
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.UniformPorts
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.OpenGraphEmbedding

/-! # Actual subforest boundary ports and fresh inactive root padding in the ambient matching -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

noncomputable def ambientWithPadding {w v : ℕ} (G : Garden w) :
    LabelledGarden w (GBranch G.tree ⊕ Fin v) := ⟨G,Function.Embedding.inl⟩

noncomputable def subforestActualPort {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) :
    Port (E.inducedGarden hc) ↪ (Fin w ⊕ (GBranch G.tree ⊕ Fin v)) × Fin 4 :=
  (subforestPortEmbedding G E hc).trans (ambientWithPadding (v := v) G).portEmbedding

/-- No genuine ambient source port uses a fresh padding-vertex label. -/
theorem subforestActualPort_ne_dummy {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (p : Port (E.inducedGarden hc))
    (j : Fin v) (i : Fin 4) : subforestActualPort G E hc p ≠ (.inr (.inr j),i) := by
  intro he
  change (ambientWithPadding (v := v) G).portEmbedding (subforestPortEmbedding G E hc p) = _ at he
  cases hq : subforestPortEmbedding G E hc p with
  | inl k =>
    rw [hq] at he
    have hv : (Sum.inl k : Fin w ⊕ (GBranch G.tree ⊕ Fin v)) = .inr (.inr j) :=
      congrArg (fun z : (Fin w ⊕ (GBranch G.tree ⊕ Fin v)) × Fin 4 => z.1) he
    cases hv
  | inr q =>
    rw [hq] at he
    have hv : (Sum.inr (Sum.inl q.1) : Fin w ⊕ (GBranch G.tree ⊕ Fin v)) = .inr (.inr j) :=
      congrArg (fun z : (Fin w ⊕ (GBranch G.tree ⊕ Fin v)) × Fin 4 => z.1) he
    cases Sum.inr.inj hv

/-- Complete source port map: actual ports use the actual rooted embedding; unused source root
ports use distinct fresh inactive ambient padding ports. -/
noncomputable def subforestOpenPort {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) : UniformPort (E.inducedGarden hc) →
      (Fin w ⊕ (GBranch G.tree ⊕ Fin v)) × Fin 4
  | (.inl j,i) => if i = 0 then subforestActualPort G E hc (.inl j) else (.inr (.inr j),i)
  | (.inr b,i) => subforestActualPort G E hc (.inr (b,i))

theorem subforestOpenPort_pad {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (p : Port (E.inducedGarden hc)) :
    subforestOpenPort G E hc (padPort (E.inducedGarden hc) p) = subforestActualPort G E hc p := by
  cases p <;> simp [subforestOpenPort,padPort]

theorem subforestOpenPort_dummy {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (j : Fin v) (i : Fin 4) (hi : i ≠ 0) :
    subforestOpenPort G E hc (.inl j,i) = (.inr (.inr j),i) := by
  simp only [subforestOpenPort,ite_eq_right hi]

theorem uniformPort_actual_or_dummy {v : ℕ} (H : Garden v) (p : UniformPort H) :
    (∃ q : Port H, p = padPort H q) ∨ ∃ j : Fin v, ∃ i : Fin 4, i ≠ 0 ∧ p = (.inl j,i) := by
  obtain ⟨a,i⟩ := p
  cases a with
  | inl j =>
    by_cases hi : i = 0
    · subst i
      exact Or.inl ⟨.inl j,rfl⟩
    · exact Or.inr ⟨j,i,hi,rfl⟩
  | inr b => exact Or.inl ⟨.inr (b,i),rfl⟩

end WaveTurbulence.Reg.Skeleton
