/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PrimeSkeletonUniqueness

/-! # Literal trivial gardens, the zero-order case of the source skeleton theorem -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- DH21-2 Definition 4.1: every source tree is trivial, with its actual root matching retained. -/
def IsTrivialGarden {w : ℕ} (G : Garden w) : Prop := G.IsPlain ∧ ∀ j, G.tree j = .leaf

theorem IsTrivialGarden.isPrimeGarden {w : ℕ} {G : Garden w} (h : IsTrivialGarden G) : IsPrimeGarden G := by
  refine ⟨h.1,?_⟩
  rintro ⟨M⟩
  have hb := M.first.2
  rw [h.2] at hb
  exact Finset.notMem_empty _ hb

end WaveTurbulence.Reg.Skeleton
