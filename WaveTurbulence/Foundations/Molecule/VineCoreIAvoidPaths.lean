/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
import Mathlib.Tactic

/-! # Explicit paths avoiding each atom of base template I -/

public section
namespace WaveTurbulence.Vine

/-- Every surviving base-I atom reaches the selected surviving root. -/
theorem coreI_avoid_paths (z v : ℕ) (hz : z<VineType.I.template.n)
    (hv : v<VineType.I.template.n) (hvz : v ≠ z) :
    AvoidPath VineType.I.template.bonds z (if z=0 then 1 else 0) v := by
  change z<2 at hz
  change v<2 at hv
  interval_cases z
  · interval_cases v
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.refl 1)
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact False.elim (hvz rfl)

end WaveTurbulence.Vine
