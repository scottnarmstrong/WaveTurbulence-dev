/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CodeEndpointLeaves

/-! # Every endpoint of a couple block lies below one of its two actual frame roots -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem couple_pair_first_below {w : ℕ} (Q : RegCpl) (a b : Address w) (p : Pair w)
    (hp : p ∈ Q.pairsAt a b) : Below a p.1 ∨ Below b p.1 := by
  have h := (couple_pair_endpoint_leaves Q a b p hp).1
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨q,_,he⟩ := Finset.mem_image.mp h
    exact Or.inl (he ▸ below_extend a q)
  · obtain ⟨q,_,he⟩ := Finset.mem_image.mp h
    exact Or.inr (he ▸ below_extend b q)

end WaveTurbulence.Reg.Skeleton
