/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleCollapseInactive
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestOpenBoundary
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestBranchRange
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.TrivialCoupleGraph
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GraphUnusedLabels

/-! # The collapsed component's exact matching is the transported actual trivial couple -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem collapseCouple_matching_inside {w : ℕ} (G : Garden w) {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b)
    (label : GBranch (decodedCouple .triv).tree ↪
      GBranch (Comb.twoRootSubforest a b (Comb.subCouple_incomparable h)).shape)
    (p : (Fin 2 ⊕ GBranch (Comb.twoRootSubforest a b (Comb.subCouple_incomparable h)).shape) × Fin 4) :
    let O := subforestOpenGraph G (Comb.twoRootSubforest a b (Comb.subCouple_incomparable h))
      (Comb.subCouple_forest_closed h)
    ((ambientWithPadding (v := 2) G).collapseCouple h).graph.mate (O.port p) =
      O.port ((LabelledGarden.mk (decodedCouple .triv) label).graph.mate p) := by
  let A := ambientWithPadding (v := 2) G
  let L := A.collapseCouple h
  let E := Comb.twoRootSubforest a b (Comb.subCouple_incomparable h)
  let O := subforestOpenGraph G E (Comb.subCouple_forest_closed h)
  let K := LabelledGarden.mk (decodedCouple .triv) label
  obtain ⟨v,i⟩ := p
  cases v with
  | inl j =>
    by_cases hi : i = 0
    · subst i
      have h0 : O.port (.inl 0,0) = A.incoming a := subforestOpenPort_root_zero G E _ 0
      have h1 : O.port (.inl 1,0) = A.incoming b := subforestOpenPort_root_zero G E _ 1
      fin_cases j
      · exact (congrArg L.graph.mate h0).trans ((A.collapseCouple_graph_left_attachment h).trans
          (h1.symm.trans (congrArg O.port (LabelledGarden.trivialCouple_root_mate label 0).symm)))
      · exact (congrArg L.graph.mate h1).trans ((A.collapseCouple_graph_right_attachment h).trans
          (h0.symm.trans (congrArg O.port (LabelledGarden.trivialCouple_root_mate label 1).symm)))
    · have hp : O.port (.inl j,i) = (.inr (.inr j),i) := subforestOpenPort_dummy G E _ j i hi
      have hn : (Sum.inr j : GBranch G.tree ⊕ Fin 2) ∉ Set.range L.label := by
        rintro ⟨d,hd⟩
        change Sum.inl (collapseCoupleBranchEmbedding h d) = Sum.inr j at hd
        cases hd
      have hfix := L.graph_unused_label (.inr j) hn i
      exact (congrArg L.graph.mate hp).trans (hfix.trans
        (hp.symm.trans (congrArg O.port (K.graph_root_inactive j i hi).symm)))
  | inr e =>
    have hp : O.port (.inr e,i) = (.inr (.inl (subforestBranchEmbedding E e)),i) :=
      subforestOpenPort_branch G E _ e i
    have hm : Below a.1 (subforestBranchEmbedding E e).1 ∨ Below b.1 (subforestBranchEmbedding E e).1 :=
      (subcoupleBranchEmbedding_range h _).mp ⟨e,rfl⟩
    have hfix := A.collapseCouple_branch_inactive h (subforestBranchEmbedding E e) hm i
    have htriv : IsTrivialGarden (decodedCouple .triv) :=
      ⟨(decodedCouple_decodes .triv).1.1,by intro j; fin_cases j <;> rfl⟩
    have hk := K.graph_branch_fixed_of_trivial htriv e i
    exact (congrArg L.graph.mate hp).trans (hfix.trans
      (hp.symm.trans (congrArg O.port hk.symm)))

end WaveTurbulence.Reg.Skeleton
