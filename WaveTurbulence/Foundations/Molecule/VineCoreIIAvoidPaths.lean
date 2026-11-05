/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
import Mathlib.Tactic

/-! # Explicit paths avoiding each atom of base template II -/

public section
namespace WaveTurbulence.Vine

/-- Every surviving base-II atom reaches the selected surviving root. -/
theorem coreII_avoid_paths (z v : ℕ) (hz : z<VineType.II.template.n)
    (hv : v<VineType.II.template.n) (hvz : v ≠ z) :
    AvoidPath VineType.II.template.bonds z (if z=0 then 1 else 0) v := by
  change z<4 at hz
  change v<4 at hv
  interval_cases z
  · interval_cases v
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.refl 1)
    · exact (Relation.EqvGen.rel 1 2 (by decide))
    · exact (Relation.EqvGen.rel 1 3 (by decide))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 3 1 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 1 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.rel 0 3 (by decide))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 1 (by decide)))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact False.elim (hvz rfl)

end WaveTurbulence.Vine
