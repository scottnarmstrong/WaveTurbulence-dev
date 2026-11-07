/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC7
import Mathlib.Tactic

/-!
# Node sets of placed codes under a root-respecting address map
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w v : ℕ}

theorem pairEndpoints_map (f : (Fin w × Path) → (Fin v × Path)) (L : List ((Fin w × Path) × (Fin w × Path))) :
    pairEndpoints (L.map (fun r => (f r.1, f r.2))) = (pairEndpoints L).image f := by
  ext z
  simp only [mem_pairEndpoints_iff, Finset.mem_image, List.mem_map]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, h | h⟩
    · exact ⟨r.1, ⟨r, hr, Or.inl rfl⟩, h.symm⟩
    · exact ⟨r.2, ⟨r, hr, Or.inr rfl⟩, h.symm⟩
  · rintro ⟨y, ⟨r, hr, h | h⟩, rfl⟩
    · exact ⟨_, ⟨r, hr, rfl⟩, Or.inl (by rw [h])⟩
    · exact ⟨_, ⟨r, hr, rfl⟩, Or.inr (by rw [h])⟩

theorem cplNodes_map (Q : RegCpl) (f : (Fin w × Path) → (Fin v × Path)) (a b : Fin w × Path)
    (ha : RespectsAt f a) (hb : RespectsAt f b) :
    cplNodes Q (f a) (f b) = (cplNodes Q a b).image f := by
  unfold cplNodes
  rw [couple_linksAt_map_local Q f a b ha hb, couple_pairsAt_map_local Q f a b ha hb,
    pairEndpoints_map, pairEndpoints_map, Finset.image_union]

theorem chainNodesSet_map (X : RegChain) (ζ : ℤˣ) (f : (Fin w × Path) → (Fin v × Path))
    (a : Fin w × Path) (ha : RespectsAt f a) :
    chainNodesSet X ζ (f a) = (chainNodesSet X ζ a).image f := by
  unfold chainNodesSet
  rw [chain_linksAt_map_local X f a ha ζ, chain_pairsAt_map_local X f a ha ζ,
    pairEndpoints_map, pairEndpoints_map, Finset.image_union]

theorem cplNodes_region {Q : RegCpl} {a b z : Fin w × Path} (hz : z ∈ cplNodes Q a b) :
    InRegion a b z := by
  unfold cplNodes at hz
  rw [← couple_branchAddresses Q a b, ← couple_leafAddresses Q a b] at hz
  simp only [Finset.mem_union] at hz
  rcases hz with (hz | hz) | (hz | hz)
  · obtain ⟨q, _, rfl⟩ := mem_image_addrExt hz; exact Or.inl (under_ext a q)
  · obtain ⟨q, _, rfl⟩ := mem_image_addrExt hz; exact Or.inr (under_ext b q)
  · obtain ⟨q, _, rfl⟩ := mem_image_addrExt hz; exact Or.inl (under_ext a q)
  · obtain ⟨q, _, rfl⟩ := mem_image_addrExt hz; exact Or.inr (under_ext b q)

theorem chainNodesSet_under {X : RegChain} {ζ : ℤˣ} {a z : Fin w × Path} (hz : z ∈ chainNodesSet X ζ a) :
    Under a z := by
  unfold chainNodesSet at hz
  have h1 := chain_branchAddresses X ζ .leaf a
  have h2 := chain_leafAddresses X ζ .leaf a
  rcases Finset.mem_union.mp hz with hz | hz
  · have : z ∈ branchAddresses (X.plug ζ .leaf) a := by rw [h1]; exact Finset.mem_union_left _ hz
    obtain ⟨q, _, rfl⟩ := mem_image_addrExt this
    exact under_ext a q
  · have : z ∈ leafAddresses (X.plug ζ .leaf) a := by rw [h2]; exact Finset.mem_union_left _ hz
    obtain ⟨q, _, rfl⟩ := mem_image_addrExt this
    exact under_ext a q

end WaveTurbulence.Stage1
