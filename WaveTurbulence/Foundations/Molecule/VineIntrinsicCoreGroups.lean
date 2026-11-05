/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreTriangles
import Mathlib.Tactic

/-! # Intrinsic recognition certificates for the pinned coherence cores

The only nonjoint core atoms without a nonjoint doubled neighbor are the
single atom in III and the exceptional pair in VII. These certificates
include the four-atom type-II template (F72).
-/

public section
namespace WaveTurbulence.Vine

/-- The literal core atom has no distinct nonjoint doubled neighbor. -/
@[expose] def CoreUndoubled (X : VineType) (i : Fin X.template.n) : Prop :=
  ∀ j : Fin X.template.n, 2 ≤ j.1 → i ≠ j →
    X.template.bonds.count (i.1,j.1)+X.template.bonds.count (j.1,i.1)<2

instance (X : VineType) (i : Fin X.template.n) : Decidable (CoreUndoubled X i) := by
  unfold CoreUndoubled
  infer_instance

/-- Two nonjoint core atoms without doubled partners belong to the same
source group. The singleton case is type III; the pair case is VII. -/
theorem template_undoubled_same_group (X : VineType) :
    ∀ i j : Fin X.template.n, 2 ≤ i.1 → 2 ≤ j.1 →
    CoreUndoubled X i → CoreUndoubled X j →
    ∃ g ∈ X.template.groups, i.1 ∈ g ∧ j.1 ∈ g := by
  cases X <;> decide

/-- An old nonjoint atom cannot meet both old rails of one insertion slot.
Shared final ports in type II are joints and are deliberately excluded. -/
theorem template_slot_nonjoint_cross_disjoint (X : VineType) :
    ∀ s ∈ X.template.slots, ∀ i : Fin X.template.n, 2 ≤ i.1 →
    (i.1=s.1.1 ∨ i.1=s.1.2) → ¬(i.1=s.2.1 ∨ i.1=s.2.2) := by
  cases X <;> decide

/-- Internal source-group edges are never among the subdivided slot edges. -/
theorem template_group_edges_unmarked (X : VineType) :
    ∀ g ∈ X.template.groups, ∀ e ∈ X.template.bonds,
    e.1 ∈ g → e.2 ∈ g → ∀ s ∈ X.template.slots,e ≠ s.1 ∧ e ≠ s.2 := by
  cases X <;> decide

/-- Core parallel multiplicity is encoded wholly in one orientation. -/
theorem template_double_oriented (X : VineType) :
    ∀ i j : Fin X.template.n,2 ≤ i.1 → 2 ≤ j.1 → i ≠ j →
    2 ≤ X.template.bonds.count (i.1,j.1)+X.template.bonds.count (j.1,i.1) →
    2 ≤ X.template.bonds.count (i.1,j.1) ∨ 2 ≤ X.template.bonds.count (j.1,i.1) := by
  cases X <;> decide

end WaveTurbulence.Vine
