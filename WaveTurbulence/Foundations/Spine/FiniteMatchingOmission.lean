/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Basic
import Mathlib.Tactic
/-! A matching admits a fixed one-endpoint omission, with no enumeration cost per decoration. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set

/-- Choose one endpoint of every edge of a finite matching. Later, the vertices are
actual type-V branch atom sets; this choice is made once per local gap table. -/
theorem exists_matching_omission {X : Type*} [Fintype X] (R : X → X → Prop)
    (hsym : ∀ ⦃a b⦄, R a b → R b a) (hirr : ∀ a, ¬ R a a)
    (hunique : ∀ a b c, R a b → R a c → b = c) :
    ∃ omitted : Set X, (∀ a ∈ omitted, ∃ b, R a b) ∧
      ∀ a b, R a b → Xor (a ∈ omitted) (b ∈ omitted) := by
  classical
  let e := Fintype.equivFin X
  let omitted : Set X := {a | ∃ b, R a b ∧ e a < e b}
  refine ⟨omitted, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hab, _⟩ := ha
    exact ⟨b, hab⟩
  · intro a b hab
    have ha : a ∈ omitted ↔ e a < e b := by
      constructor
      · rintro ⟨c, hac, hlt⟩
        exact hunique a c b hac hab ▸ hlt
      · intro hlt
        exact ⟨b, hab, hlt⟩
    have hb : b ∈ omitted ↔ e b < e a := by
      constructor
      · rintro ⟨c, hbc, hlt⟩
        exact hunique b c a hbc (hsym hab) ▸ hlt
      · intro hlt
        exact ⟨a, hsym hab, hlt⟩
    have hne : e a ≠ e b := by
      intro he
      have habne : a ≠ b := by
        rintro rfl
        exact hirr _ hab
      exact habne (e.injective he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨ha.mpr hlt, fun h => (not_lt_of_ge hlt.le) (hb.mp h)⟩
    · exact Or.inr ⟨hb.mpr hgt, fun h => (not_lt_of_ge hgt.le) (ha.mp h)⟩

end WaveTurbulence.LGSpine
