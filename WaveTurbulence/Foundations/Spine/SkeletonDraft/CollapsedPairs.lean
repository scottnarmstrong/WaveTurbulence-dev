/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourcePairsImage
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsePairedTreeGarden

/-! # Exact pair-set transport for collapse of an embedded paired tree -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- The collapsed matching transports to exactly the original pairs outside the removed interval. -/
theorem collapsePairedTreeGarden_pairs {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) :
    (sourcePairs (collapsePairedTreeGarden h)).image
      (fun p => (stretch a.1 (Comb.collapseDataOfDesc h.1).path p.1,
        stretch a.1 (Comb.collapseDataOfDesc h.1).path p.2)) =
    (sourcePairs G).filter (fun p => ∃ ℓ : GLeaf G.tree,
      ℓ.1 = p.1 ∧ ℓ ∉ a.leavesBelow \ b.leavesBelow) := by
  classical
  rw [sourcePairs_image_of_embedding (collapsePairedTreeGarden h) G
    (pairedTreeLeafEmbedding h) _ (pairedTreeLeafEmbedding_sign h)
    (fun _ => rfl) (collapsePairedTreeGarden_pair h)]
  apply Finset.filter_congr
  intro p hp
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨pairedTreeLeafEmbedding h x,hx,
      (pairedTreeLeafEmbedding_range h _).mp ⟨x,rfl⟩⟩
  · rintro ⟨ℓ,hℓ,hm⟩
    obtain ⟨x,hx⟩ := (pairedTreeLeafEmbedding_range h ℓ).mpr hm
    exact ⟨x,(congrArg (fun z : GLeaf G.tree => z.1) hx).trans hℓ⟩

end WaveTurbulence.Reg.Skeleton
