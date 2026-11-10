/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.MoleculeOverlapClassification
public import WaveTurbulence.Foundations.Spine.SourceJointPairUniqueness
public import WaveTurbulence.Foundations.Spine.VineDelObjects
/-! Two distinct ordinary blocks sharing a joint with different dart pairs are not nested and
overlap in exactly the same-joints or one-common-joint shape (DH23 Lemma 4.11). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Direct-adjacency connectivity of an ordinary block gives the induced version. -/
theorem groupConnected_of_block {M : Molecule V D} {S : Finset V} {a b : V}
    (hB : M.IsBlock S a b) : Mole.GroupConnected M S := by
  refine ⟨⟨a, hB.2.1⟩, fun u hu v hv => ?_⟩
  have hp := hB.2.2.2.2.2.2.2.2.2 u hu v hv
  have key : ∀ p q, Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧
      M.atom (M.mate x) = b) p q → p = q ∨ (p ∈ S ∧ q ∈ S ∧ (Mole.induced M S).SameComponent p q) := by
    intro p q h
    induction h with
    | rel a b hab =>
      obtain ⟨x, hx, rfl, rfl⟩ := hab
      exact Or.inr ⟨hx.1, hx.2, Relation.EqvGen.rel _ _
        ((Mole.induced_adj_iff M S _ _).mpr ⟨⟨x, rfl, rfl⟩, hx.1, hx.2⟩)⟩
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
      rcases ih with rfl | ⟨h1, h2, h3⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h2, h1, Relation.EqvGen.symm _ _ h3⟩
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with rfl | ⟨h1, h2, h3⟩
      · exact ih2
      · rcases ih2 with rfl | ⟨h4, h5, h6⟩
        · exact Or.inr ⟨h1, h2, h3⟩
        · exact Or.inr ⟨h1, h5, Relation.EqvGen.trans _ _ _ h3 h6⟩
  rcases key u v hp with rfl | ⟨_, _, h⟩
  · exact Relation.EqvGen.refl _
  · exact h

end WaveTurbulence.LGSpine
