/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawPairSite

/-! # Every other canonical edge avoids both endpoints of a typed source pair -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Raw.Valid.pair_ne_endpoints {w : ℕ} {R : Raw w} (hR : R.Valid)
    {x y : Address w} (hxy : R.PairSite x y) (p : Pair w) (hp : p ∈ R.pairs)
    (hne : p ≠ (x,y)) : p.1 ≠ x ∧ p.1 ≠ y ∧ p.2 ≠ x ∧ p.2 ≠ y := by
  have hx (he : p.1 = x ∨ p.2 = x) : p = (x,y) :=
    (edgeAt_unique R hR ⟨x,hxy.leftLeaf⟩ p hp he).trans
      (edgeAt_unique R hR ⟨x,hxy.leftLeaf⟩ (x,y) hxy.pair_mem (Or.inl rfl)).symm
  have hy (he : p.1 = y ∨ p.2 = y) : p = (x,y) :=
    (edgeAt_unique R hR ⟨y,hxy.rightLeaf⟩ p hp he).trans
      (edgeAt_unique R hR ⟨y,hxy.rightLeaf⟩ (x,y) hxy.pair_mem (Or.inr rfl)).symm
  exact ⟨fun h => hne (hx (Or.inl h)),fun h => hne (hy (Or.inl h)),
    fun h => hne (hx (Or.inr h)),fun h => hne (hy (Or.inr h))⟩

end WaveTurbulence.Reg.Skeleton
