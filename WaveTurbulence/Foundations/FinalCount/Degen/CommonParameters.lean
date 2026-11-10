/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Removal
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-! # Uniform post-removal parameters, determined only by the common label -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Exact degree loss, counting self-loop darts correctly. -/
theorem deg_eraseAtoms_add_removed (M : Molecule V D) (Y : Finset V) {z : V} (hz : z ∉ Y) :
    (eraseAtoms M Y).deg z + (removedDartsAt M Y z).card = M.deg z := by
  have hs := sum_dartsAt_split M Y hz (fun _ => (1 : ℕ))
  simpa only [sum_const, smul_eq_mul, nsmul_eq_mul, mul_one, Molecule.deg] using hs.symm

end WaveTurbulence.Degen
