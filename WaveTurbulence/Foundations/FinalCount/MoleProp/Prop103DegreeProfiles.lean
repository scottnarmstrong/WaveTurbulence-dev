/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBasic

/-! # The literal preliminary degree profiles of DH23 Proposition10.3 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Exactly two degree-three atoms; all other actual atoms have degree four. -/
def TwoThreeProfile (M : Molecule V D) : Prop :=
  ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧ M.deg b = 3 ∧
    ∀ z ∈ M.atoms, z ≠ a → z ≠ b → M.deg z = 4

/-- Exactly one degree-two atom; all other actual atoms have degree four. -/
def OneTwoProfile (M : Molecule V D) : Prop :=
  ∃ a ∈ M.atoms, M.deg a = 2 ∧ ∀ z ∈ M.atoms, z ≠ a → M.deg z = 4

end WaveTurbulence.MoleProp
