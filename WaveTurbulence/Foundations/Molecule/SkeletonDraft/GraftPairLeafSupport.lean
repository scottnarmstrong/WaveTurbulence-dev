/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CodeEndpointLeaves
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.GraftPairLeafEquiv

/-! # Literal old and inserted leaf addresses in a two-root graft forest -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem graftPair_old_leaf {w : ℕ} (tree : Fin w → TTree) (ℓ q : GLeaf tree)
    (hne : q ≠ ℓ) (s r : TTree) (z : GLeaf tree) (hzℓ : z ≠ ℓ) (hzq : z ≠ q) :
    z.1.2 ∈ (Comb.graftLeafPairForest tree ℓ q hne s r z.1.1).leaves :=
  (Comb.graftPairLeafEquiv tree ℓ q hne s r (.inl (.inl ⟨z,hzℓ,hzq⟩))).2

theorem graftPair_inserted_leaf {w : ℕ} (tree : Fin w → TTree) (ℓ q : GLeaf tree)
    (hne : q ≠ ℓ) (s r : TTree) (z : Address w)
    (hz : z ∈ leafAddresses s ℓ.1 ∪ leafAddresses r q.1) :
    z.2 ∈ (Comb.graftLeafPairForest tree ℓ q hne s r z.1).leaves := by
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact (Comb.graftPairLeafEquiv tree ℓ q hne s r (.inl (.inr ⟨(0,p),hp⟩))).2
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact (Comb.graftPairLeafEquiv tree ℓ q hne s r (.inr ⟨(0,p),hp⟩)).2

end WaveTurbulence.Reg.Skeleton
