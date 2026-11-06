/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleCollapseGraphEdges

/-! # Every branch inside an arbitrary collapsed couple becomes an inactive original label -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem collapseCouple_branch_inactive {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b)
    (d : GBranch G.garden.tree) (hd : Below a.1 d.1 ∨ Below b.1 d.1) (i : Fin 4) :
    (G.collapseCouple h).graph.mate (.inr (G.label d),i) = (.inr (G.label d),i) := by
  apply extendMate_outside
  rintro ⟨p,hp⟩
  cases p with
  | inl j =>
    have he : (Sum.inl j : Fin w ⊕ B) = .inr (G.label d) := congrArg (fun z : (Fin w ⊕ B) × Fin 4 => z.1) hp
    cases he
  | inr p =>
    have he : collapseCoupleBranchEmbedding h p.1 = d :=
      G.label.injective (Sum.inr.inj (congrArg (fun z : (Fin w ⊕ B) × Fin 4 => z.1) hp))
    have hv : p.1.1 = d.1 := congrArg (fun e : GBranch G.garden.tree => e.1) he
    have hn := ((collapsePairForest_branch_iff G.garden.tree a b (Comb.subCouple_incomparable h) p.1.1).mp p.1.2).2
    rcases hd with hd | hd
    · exact hn.1 (hv.symm ▸ hd)
    · exact hn.2 (hv.symm ▸ hd)

end WaveTurbulence.Reg.Skeleton.LabelledGarden
