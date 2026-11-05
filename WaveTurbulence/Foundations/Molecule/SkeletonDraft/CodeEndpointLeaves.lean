/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Literal code endpoints are leaves of their extracted filled components -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem leafAddresses_subtree_valid {w : ℕ} (tree : Fin w → TTree) (a : Address w) (u : TTree)
    (ha : Comb.subtree (tree a.1) a.2 = some u) (z : Address w) (hz : z ∈ leafAddresses u a) :
    z.2 ∈ (tree z.1).leaves := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  exact (Comb.subtree_leaves_iff ha p).mp hp

theorem couple_pair_endpoint_leaves {w : ℕ} (Q : RegCpl) (a b : Address w) (p : Pair w)
    (hp : p ∈ Q.pairsAt a b) :
    (p.1 ∈ leafAddresses Q.trees.1 a ∪ leafAddresses Q.trees.2 b) ∧
    (p.2 ∈ leafAddresses Q.trees.1 a ∪ leafAddresses Q.trees.2 b) := by
  simp only [couple_leafAddresses]
  exact ⟨(mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inl rfl⟩,
    (mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inr rfl⟩⟩

theorem chain_pair_endpoint_leaves {w : ℕ} (X : RegChain) (ζ : ℤˣ) (t : TTree)
    (a : Address w) (p : Pair w) (hp : p ∈ X.pairsAt ζ a) :
    p.1 ∈ leafAddresses (X.plug ζ t) a ∧ p.2 ∈ leafAddresses (X.plug ζ t) a := by
  simp only [chain_leafAddresses]
  exact ⟨Finset.mem_union_left _ ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inl rfl⟩),
    Finset.mem_union_left _ ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inr rfl⟩)⟩

end WaveTurbulence.Reg.Skeleton
