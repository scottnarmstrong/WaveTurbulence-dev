/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBBranches
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourcePrimeGraph

/-! # Exact surviving labelled port family under actual B-mini collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem miniB_port_range {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniTreeCode} (h : MiniBOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) (x : (Fin w ⊕ B) × Fin 4) :
    x ∈ Set.range (G.collapsePairedTree (h.isSubPairedTree hG)).portEmbedding ↔
      x ∈ Set.range G.portEmbedding ∧ x.1 ≠ .inr (G.label b) ∧ x.1 ≠ .inr (G.label c) := by
  constructor
  · rintro ⟨p,rfl⟩
    cases p with
    | inl j => exact ⟨⟨.inl j,rfl⟩,by simp [portEmbedding],by simp [portEmbedding]⟩
    | inr p =>
      obtain ⟨d,i⟩ := p
      let e := collapsePairedTreeBranchEmbedding (h.isSubPairedTree hG) d
      have he : e ∈ Set.range (collapsePairedTreeBranchEmbedding (h.isSubPairedTree hG)) := ⟨d,rfl⟩
      have hn := (h.branch_embedding_range hG e).mp he
      refine ⟨⟨.inr (e,i),rfl⟩,?_,?_⟩
      · intro he
        exact hn.1 (G.label.injective (Sum.inr.inj he))
      · intro he
        exact hn.2 (G.label.injective (Sum.inr.inj he))
  · rintro ⟨⟨p,rfl⟩,hb,hc⟩
    cases p with
    | inl j => exact ⟨.inl j,rfl⟩
    | inr p =>
      obtain ⟨d,i⟩ := p
      have hd : d ≠ b ∧ d ≠ c := by
        constructor
        · rintro rfl
          exact hb rfl
        · rintro rfl
          exact hc rfl
      obtain ⟨e,he⟩ := (h.branch_embedding_range hG d).mpr hd
      refine ⟨.inr (e,i),?_⟩
      change (Sum.inr (G.label (collapsePairedTreeBranchEmbedding (h.isSubPairedTree hG) e)),i) =
        (Sum.inr (G.label d),i)
      rw [he]

end WaveTurbulence.Reg.Skeleton.LabelledGarden
