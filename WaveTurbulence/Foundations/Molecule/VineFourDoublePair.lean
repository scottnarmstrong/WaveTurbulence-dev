/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDoublePairClosure
import Mathlib.Tactic

/-! # Extract the actual doubled pair from a full rung incidence row -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*}

/-- The first two entries of a full rung row are two distinct darts to
its actual paired atom. -/
@[expose] def FourIncidences.doublePair {M : Molecule V D} {x y p q : V}
    (R : FourIncidences M x ![y,y,p,q]) : TwoIncidences M x y where
  dart := fun i => R.dart (Fin.castLE (by decide : 2 ≤ 4) i)
  injective := R.injective.comp (Fin.castLE_injective (by decide : 2 ≤ 4))
  atom_eq := fun i => R.atom_eq _
  neighbor_eq := by
    intro i
    fin_cases i
    · exact R.neighbor_eq 0
    · exact R.neighbor_eq 1

/-- Changing one endpoint of an unordered pair changes the pair. -/
theorem sym2_pair_ne_of_right_ne {V : Type*} (x : V) {y z : V} (hne : y ≠ z) :
    s(x,y) ≠ s(x,z) := by
  intro he
  rcases Sym2.eq_iff.mp he with h | h
  · exact hne h.2
  · exact hne (h.2.trans h.1)

end WaveTurbulence.Vine
