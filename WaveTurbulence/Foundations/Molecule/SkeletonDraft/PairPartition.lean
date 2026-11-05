/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Carrier

/-! # Decomposition of actual oriented source pairs along a leaf family -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- Reading a paired leaf is literal sign orientation of its two actual addresses. -/
theorem sourcePairAt_eq_orient {w : ℕ} (G : Garden w) (ℓ : GLeaf G.tree) :
    sourcePairAt G ℓ = orient ℓ.1 (nodeSign G.sig ℓ.1) (G.pair ℓ).1 := rfl

/-- Reading an actual edge from its other endpoint gives the same canonical orientation. -/
theorem sourcePairAt_pair {w : ℕ} (G : Garden w) (hG : G.IsPlain) (ℓ : GLeaf G.tree) :
    sourcePairAt G (G.pair ℓ) = sourcePairAt G ℓ := by
  symm
  apply sourcePairs_eq_at G hG _ (sourcePairAt_mem G hG ℓ) (G.pair ℓ)
  unfold sourcePairAt
  split_ifs <;> simp

/-- The pairs whose positive endpoint survives, together with the edges of the removed leaves,
recover exactly the original matching. This identity does not require enumerating the leaf family. -/
theorem sourcePairs_partition {w : ℕ} (G : Garden w) (hG : G.IsPlain)
    (L : Finset (GLeaf G.tree)) :
    (sourcePairs G).filter (fun p => ∃ ℓ : GLeaf G.tree, ℓ.1 = p.1 ∧ ℓ ∉ L) ∪
      L.image (sourcePairAt G) = sourcePairs G := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hp
      exact sourcePairAt_mem G hG ℓ
  · intro hp
    obtain ⟨ℓ,hℓ,he⟩ := Finset.mem_image.mp hp
    by_cases hm : ℓ ∈ L
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨ℓ,hm,?_⟩
      rw [sourcePairAt,if_pos (Finset.mem_filter.mp hℓ).2]
      exact he
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hp,ℓ,congrArg Prod.fst he,hm⟩

end WaveTurbulence.Reg.Skeleton
