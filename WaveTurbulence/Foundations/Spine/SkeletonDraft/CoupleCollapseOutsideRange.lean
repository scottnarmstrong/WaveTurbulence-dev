/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleCollapseActiveEdges
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleCollapseInactive
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestBranchRange

/-! # Every original ambient port outside the collapsed component survives literally -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem collapseCouple_port_survives_outside {w : ℕ} (G : Garden w) {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (x : (Fin w ⊕ (GBranch G.tree ⊕ Fin 2)) × Fin 4)
    (hx : x ∉ Set.range (subforestOpenGraph G (Comb.twoRootSubforest a b (Comb.subCouple_incomparable h))
      (Comb.subCouple_forest_closed h)).port)
    (ha : x ∈ Set.range (ambientWithPadding (v := 2) G).portEmbedding) :
    x ∈ Set.range ((ambientWithPadding (v := 2) G).collapseCouple h).portEmbedding := by
  let A := ambientWithPadding (v := 2) G
  let L := A.collapseCouple h
  let E := Comb.twoRootSubforest a b (Comb.subCouple_incomparable h)
  let O := subforestOpenGraph G E (Comb.subCouple_forest_closed h)
  obtain ⟨p,rfl⟩ := ha
  cases p with
  | inl j =>
    let n := GNode.root L.garden.tree j
    have hi : L.incoming n = (.inl j,0) :=
      (A.collapseCouple_incoming h n).trans
        ((congrArg A.incoming (show collapseCoupleNodeEmbedding h n = GNode.root G.tree j from Subtype.ext rfl)).trans
          (A.incoming_root j))
    exact ⟨encodeIncidence L.garden (.inl n),hi⟩
  | inr p =>
    obtain ⟨d,i⟩ := p
    by_cases hd : ¬ Below a.1 d.1 ∧ ¬ Below b.1 d.1
    · let e : GBranch L.garden.tree := ⟨d.1,
        (collapsePairForest_branch_iff G.tree a b (Comb.subCouple_incomparable h) d.1).mpr ⟨d.2,hd⟩⟩
      refine ⟨.inr (e,i),?_⟩
      have he : collapseCoupleBranchEmbedding h e = d := Subtype.ext rfl
      exact congrArg (fun d => (Sum.inr (A.label d),i)) he
    · have hinside : Below a.1 d.1 ∨ Below b.1 d.1 := by tauto
      obtain ⟨e,he⟩ := (subcoupleBranchEmbedding_range h d).mpr hinside
      have hp : O.port (.inr e,i) = (.inr (.inl d),i) :=
        (subforestOpenPort_branch G E (Comb.subCouple_forest_closed h) e i).trans
          (congrArg (fun d => (Sum.inr (Sum.inl d),i)) he)
      exact (hx ⟨(.inr e,i),hp⟩).elim

end WaveTurbulence.Reg.Skeleton
