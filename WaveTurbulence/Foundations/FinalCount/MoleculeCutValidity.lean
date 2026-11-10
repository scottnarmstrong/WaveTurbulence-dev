/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.MoleculeCuts
public import WaveTurbulence.Foundations.Molecule.MoleculeDecorations
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
import Mathlib.Tactic

/-!
# Actual half-edge cuts preserve the molecule axioms

TARGET `defcut`: orientation bounds follow from the degree split. A new
saturated component cannot occur: it would avoid both degree-at-most-two
cut atoms and would already be a saturated component of the old molecule.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  (M : Molecule V D) {v v2 : V} {x1 x2 : D}

omit [Fintype D] in
/-- A cut either keeps an incidence at its old atom or moves it from v to v2. -/
theorem cut_atom_cases (x : D) :
    (M.cut v v2 x1 x2).atom x = M.atom x ∨
      (M.atom x = v ∧ (M.cut v v2 x1 x2).atom x = v2) := by
  by_cases hx : M.atom x = v ∧ x ≠ x1 ∧ x ≠ x2
  · exact Or.inr ⟨hx.1,by simp [Molecule.cut,hx.1,hx.2.1,hx.2.2]⟩
  · exact Or.inl (by simp only [Molecule.cut,hx,ite_false])

end WaveTurbulence.Mole
