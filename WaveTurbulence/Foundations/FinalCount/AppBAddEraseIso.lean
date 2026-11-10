/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIsoComponents
import Mathlib.Tactic

/-! # A newly added bond can be deleted literally -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Adding a bond between existing atoms, then deleting that same bond,
gives a full atom-and-half-edge isomorphism to the original molecule. -/
@[expose] noncomputable def appbEraseAddedBondIso (M : Molecule V D) (a b : V)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) :
    DirectedMoleculeIso M (eraseBond (addBond M a b) (.inr true)) := by
  let N := eraseBond (addBond M a b) (.inr true)
  have hatoms : N.atoms = M.atoms := by
    change insert a (insert b M.atoms) = M.atoms
    simp only [insert_eq_of_mem ha,insert_eq_of_mem hb]
  let atomEquiv : M.atoms ≃ N.atoms := {
    toFun := fun v => ⟨v.val,hatoms.symm ▸ v.property⟩
    invFun := fun v => ⟨v.val,hatoms ▸ v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let f : D → {x : D ⊕ Bool // x ≠ Sum.inr true ∧ x ≠ (addBond M a b).mate (.inr true)} :=
    fun x => ⟨.inl x,by constructor <;> intro h <;> cases h⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      exact Sum.inl.inj (congrArg Subtype.val h)
    · intro x
      obtain ⟨x,hx⟩ := x
      cases x with
      | inl x => exact ⟨x,rfl⟩
      | inr t =>
        cases t
        · exact (hx.2 rfl).elim
        · exact (hx.1 rfl).elim
  exact {
    atoms := atomEquiv
    darts := Equiv.ofBijective f hbij
    atom_comm := fun _ => rfl
    mate_comm := fun _ => rfl
    out_comm := fun _ => rfl }

end WaveTurbulence.Mole
