/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreMasks
public import WaveTurbulence.Foundations.Molecule.VineIncidence
import Mathlib.Tactic

/-! # Degree masks are the actual degrees of induced template subsets -/

public section
namespace WaveTurbulence.Vine

/-- The 0/1 membership mask of a finite atom set. -/
@[expose] def membershipMask (S : Finset ℕ) (v : ℕ) : ℕ := if v ∈ S then 1 else 0

end WaveTurbulence.Vine
