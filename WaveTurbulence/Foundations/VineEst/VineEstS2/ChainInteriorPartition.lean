/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Basic

/-! # Interior partition at an actual source-chain concatenation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

/-- Removing the upper joint assigns a shared joint to the upper ingredient.
These are precisely the defining source concatenation premises. -/
theorem chainInterior_union {V : Type*} [DecidableEq V] (S T : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hi : S ∩ T = {b}) :
    (S ∪ T).erase a = S.erase a ∪ T.erase b := by
  classical
  have haT : a ∉ T := by
    intro haT
    have he := Finset.mem_inter.mpr ⟨ha,haT⟩
    rw [hi,Finset.mem_singleton] at he
    exact hab he
  ext v
  simp only [Finset.mem_erase,Finset.mem_union]
  constructor
  · rintro ⟨hva,hvS | hvT⟩
    · exact Or.inl ⟨hva,hvS⟩
    · by_cases hvb : v = b
      · subst v
        exact Or.inl ⟨Ne.symm hab,hb⟩
      · exact Or.inr ⟨hvb,hvT⟩
  · rintro (⟨hva,hvS⟩ | ⟨hvb,hvT⟩)
    · exact ⟨hva,Or.inl hvS⟩
    · exact ⟨fun he => haT (he ▸ hvT),Or.inr hvT⟩

theorem chainInterior_disjoint {V : Type*} [DecidableEq V] (S T : Finset V) (a b : V)
    (hi : S ∩ T = {b}) : Disjoint (S.erase a) (T.erase b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvS hvT
  have he := Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hvS).2,(Finset.mem_erase.mp hvT).2⟩
  rw [hi,Finset.mem_singleton] at he
  exact (Finset.mem_erase.mp hvT).1 he

theorem chainInterior_card {V : Type*} [DecidableEq V] (S T : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hi : S ∩ T = {b}) :
    ((S ∪ T).erase a).card = (S.erase a).card+(T.erase b).card := by
  rw [chainInterior_union S T a b ha hb hab hi]
  exact Finset.card_union_of_disjoint (chainInterior_disjoint S T a b hi)

end WaveTurbulence.VineEstS2
