/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.EmbeddedPairedTreePairing

/-! # Exact lower marking of the actual source embedded paired tree -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem embeddedPairedTree_mark {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) (ℓ : GLeaf (Comb.embeddedPairedTree h).tree) :
    (Comb.embeddedPairedTree h).mark ℓ =
      if ℓ.1.2 = (Comb.collapseDataOfDesc h.1).path then some MarkTag.lower else none := by
  classical
  let D := Comb.collapseDataOfDesc h.1
  simp only [Comb.embeddedPairedTree,Comb.pairedTreeFromLeafEmbedding,Comb.pairedTreeWithLone]
  have he : ℓ = Comb.collapsedLone D.lower_eq ↔ ℓ.1.2 = D.path := by
    constructor
    · intro he
      exact congrArg (fun z : GLeaf (Comb.embeddedPairedTree h).tree => z.1.2) he
    · intro he
      exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) he)
  by_cases hl : ℓ = Comb.collapsedLone D.lower_eq
  · exact (ite_eq_left hl).trans (ite_eq_left (he.mp hl)).symm
  · exact (ite_eq_right hl).trans (ite_eq_right (fun hp => hl (he.mpr hp))).symm

end WaveTurbulence.Reg.Skeleton
