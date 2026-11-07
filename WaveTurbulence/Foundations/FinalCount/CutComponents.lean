/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutBasics
/-! Component count of a cut (FINALCOUNT-G2 step 1): `F ≤ F_cut ≤ F + 1`, with `F_cut = F` iff the two
halves stay connected. Hence `χ_cut = χ - 1` for an α-cut and `χ_cut = χ` for a β-cut (see `CutRank`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- `Quot.mk` of atoms identifies exactly the atoms in the same component. -/
theorem quot_mk_eq_iff (N : Molecule V D) (a b : V) (ha : a ∈ N.atoms) (hb : b ∈ N.atoms) :
    (Quot.mk (fun u w : N.atoms => N.Adj u.1 w.1) ⟨a, ha⟩ = Quot.mk _ ⟨b, hb⟩) ↔ N.SameComponent a b := by
  constructor
  · intro h
    have h1 := Quot.eqvGen_exact h
    have : ∀ p q : N.atoms, Relation.EqvGen (fun u w : N.atoms => N.Adj u.1 w.1) p q →
        N.SameComponent p.1 q.1 := by
      intro p q hpq
      induction hpq with
      | rel _ _ h => exact Relation.EqvGen.rel _ _ h
      | refl _ => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    exact this _ _ h1
  · intro h
    have key : ∀ a b, N.SameComponent a b → a = b ∨ ∃ (ha : a ∈ N.atoms) (hb : b ∈ N.atoms),
        (Quot.mk (fun u w : N.atoms => N.Adj u.1 w.1) ⟨a, ha⟩ = Quot.mk _ ⟨b, hb⟩) := by
      intro a b hab
      induction hab with
      | rel x y hxy =>
        right
        obtain ⟨z, hz1, hz2⟩ := hxy
        have h1 : x ∈ N.atoms := hz1 ▸ N.atom_mem z
        have h2 : y ∈ N.atoms := hz2 ▸ N.atom_mem (N.mate z)
        exact ⟨h1, h2, Quot.sound ⟨z, hz1, hz2⟩⟩
      | refl x => exact Or.inl rfl
      | symm x y _ ih =>
        rcases ih with rfl | ⟨h1, h2, e⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h2, h1, e.symm⟩
      | trans x y z _ _ ih1 ih2 =>
        rcases ih1 with rfl | ⟨h1, h2, e1⟩
        · exact ih2
        · rcases ih2 with rfl | ⟨h3, h4, e2⟩
          · exact Or.inr ⟨h1, h2, e1⟩
          · exact Or.inr ⟨h1, h4, e1.trans e2⟩
    rcases key a b h with rfl | ⟨h1, h2, e⟩
    · rfl
    · exact e

end WaveTurbulence.FinalCount
