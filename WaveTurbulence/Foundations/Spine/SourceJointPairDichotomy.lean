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

/-- If two distinct ordinary blocks share a joint `v` and use different oriented dart pairs there,
they are not nested and are in the same-joints or one-joint overlap shape. -/
theorem joint_pair_dichotomy {M : Molecule V D} (hM : M.IsMolecule) {A B : Finset V}
    {a1 a2 b1 b2 : V} (hA : M.IsBlock A a1 a2) (hB : M.IsBlock B b1 b2)
    (hdA : Mole.InteriorDeletionProperty M A a1 a2) (hdB : Mole.InteriorDeletionProperty M B b1 b2)
    (hiA : ∀ x ∈ A \ {a1, a2}, ∀ y ∈ A \ {a1, a2},
      (Mole.induced M (A \ {a1, a2})).SameComponent x y)
    (hiB : ∀ x ∈ B \ {b1, b2}, ∀ y ∈ B \ {b1, b2},
      (Mole.induced M (B \ {b1, b2})).SameComponent x y)
    {v : V} (hvA : v = a1 ∨ v = a2) (hvB : v = b1 ∨ v = b2) {x y x' y' : D}
    (hxy : SourceJointPair M A v x y) (hxy' : SourceJointPair M B v x' y')
    (hne : ¬ (x = x' ∧ y = y')) :
    ¬ A ⊆ B ∧ ¬ B ⊆ A ∧
    ((({a1, a2} : Finset V) = {b1, b2} ∧ A ∩ B = {a1, a2}) ∨
      (({a1, a2} : Finset V) ≠ {b1, b2} ∧ ∃ a b c : V, ({a1, a2} : Finset V) = {a, c} ∧
        ({b1, b2} : Finset V) = {b, c} ∧ a ≠ b ∧ A ∩ B = {c} ∧
        (M.IsBlock (A ∪ B) a b ∨ Mole.IsHyperBlock M (A ∪ B) a b))) := by
  have hnAB : ¬ A ⊆ B := fun h =>
    hne (source_nested_joint_pairs_compatible M h hB hvB hxy hxy')
  have hnBA : ¬ B ⊆ A := fun h =>
    (fun hh => hne ⟨hh.1.symm, hh.2.symm⟩) (source_nested_joint_pairs_compatible M h hA hvA hxy' hxy)
  have hne' : (A ∩ B).Nonempty := ⟨v, mem_inter.mpr ⟨hxy.2.2.1.1 |> fun h => by
    have := hxy.1 ▸ h; exact this, hxy'.1 ▸ hxy'.2.2.1.1⟩⟩
  obtain ⟨_, _, hcl⟩ := Mole.molecule_overlap_classification M hM
    (Mole.BlockRealization.block hA (groupConnected_of_block hA))
    (Mole.BlockRealization.block hB (groupConnected_of_block hB)) hne' hnAB hnBA hdA hdB hiA hiB
  refine ⟨hnAB, hnBA, ?_⟩
  rcases hcl with ⟨h1, h2, _⟩ | ⟨h1, _, a, b, c, h2, h3, h4, _, _, h5, h6⟩ | ⟨hdis, _⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, a, b, c, h2, h3, h4, h5, h6⟩
  · exfalso
    have hv : v ∈ ({a1, a2} : Finset V) ∩ {b1, b2} := by
      simp only [mem_inter, mem_insert, mem_singleton]; exact ⟨hvA, hvB⟩
    exact (Finset.disjoint_left.mp hdis) (mem_inter.mp hv).1 (mem_inter.mp hv).2

end WaveTurbulence.LGSpine
