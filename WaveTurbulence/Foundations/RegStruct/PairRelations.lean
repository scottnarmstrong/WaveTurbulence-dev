/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainAttach

/-! # Pair-relation fidelity of terminal normalization (DH21 Proposition 4.10)

Source histories carry lists in chronological order. Garden matching sees the
unordered pair relation, so normalization must preserve that relation as well
as both tree shapes.
-/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Reading a list as unordered pairs is precisely membership in either orientation. -/
theorem mem_symmPairs_iff {α : Type*} (P : List (α × α)) (z : α × α) :
    z ∈ symmPairs P ↔ z ∈ P ∨ z.swap ∈ P := by
  simp only [symmPairs, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨p,hp,hpz⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [← hpz]; simpa only [Prod.swap_swap] using hp)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨z.swap,h,Prod.swap_swap z⟩

/-- Membership equality of oriented lists preserves their unordered relations. -/
theorem symmPairs_congr {α : Type*} {P Q : List (α × α)}
    (h : ∀ z, z ∈ P ↔ z ∈ Q) (z) : z ∈ symmPairs P ↔ z ∈ symmPairs Q := by
  rw [mem_symmPairs_iff, mem_symmPairs_iff, h z, h z.swap]

/-- A garden's matching predicate depends only on the trees and the unordered relation. -/
theorem matchesCouple_congr (G : Garden 2) {T S : TTree × TTree}
    {P Q : List ((Fin 2 × Path) × (Fin 2 × Path))}
    (ht : T = S) (hp : ∀ z, z ∈ P ↔ z ∈ Q) :
    G.MatchesCouple T P ↔ G.MatchesCouple S Q := by
  subst S
  constructor
  · rintro ⟨hg,h₀,h₁,hpair⟩
    exact ⟨hg,h₀,h₁,fun ℓ => (symmPairs_congr hp _).mp (hpair ℓ)⟩
  · rintro ⟨hg,h₀,h₁,hpair⟩
    exact ⟨hg,h₀,h₁,fun ℓ => (symmPairs_congr hp _).mpr (hpair ℓ)⟩

end WaveTurbulence.Reg
