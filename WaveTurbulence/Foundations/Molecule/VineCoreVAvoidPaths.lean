/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
import Mathlib.Tactic

/-! # Explicit paths avoiding each atom of base template V -/

public section
namespace WaveTurbulence.Vine

/-- Every surviving base-V atom reaches the selected surviving root. -/
theorem coreV_avoid_paths (z v : ℕ) (hz : z<VineType.V.template.n)
    (hv : v<VineType.V.template.n) (hvz : v ≠ z) :
    AvoidPath VineType.V.template.bonds z (if z=0 then 1 else 0) v := by
  change z<9 at hz
  change v<9 at hv
  interval_cases z
  · interval_cases v
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.refl 1)
    · exact (Relation.EqvGen.trans 1 3 2 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.rel 3 2 (by decide)))
    · exact (Relation.EqvGen.rel 1 3 (by decide))
    · exact (Relation.EqvGen.trans 1 3 4 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 2 4 (Relation.EqvGen.rel 3 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))))
    · exact (Relation.EqvGen.trans 1 3 5 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 1 3 6 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 2 6 (Relation.EqvGen.rel 3 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide)))))
    · exact (Relation.EqvGen.trans 1 3 7 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 7 (by decide))))
    · exact (Relation.EqvGen.trans 1 3 8 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 8 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 7 8 (Relation.EqvGen.rel 5 7 (by decide)) (Relation.EqvGen.rel 7 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 7 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 7 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.rel 0 1 (by decide))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.rel 1 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 1 4 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 4 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 4 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide)))))
    · exact (Relation.EqvGen.trans 0 1 5 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 5 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 1 6 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 6 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 6 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 4 6 (Relation.EqvGen.rel 5 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))))
    · exact (Relation.EqvGen.trans 0 1 7 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 7 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 7 (by decide)))))
    · exact (Relation.EqvGen.trans 0 1 8 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 8 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 8 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 7 8 (Relation.EqvGen.rel 5 7 (by decide)) (Relation.EqvGen.rel 7 8 (by decide))))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.rel 0 1 (by decide))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 5 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 5 7 (Relation.EqvGen.rel 4 5 (by decide)) (Relation.EqvGen.rel 5 7 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.rel 0 1 (by decide))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.rel 1 3 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 1 5 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 5 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 1 6 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 6 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 6 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 7 6 (Relation.EqvGen.rel 5 7 (by decide)) (Relation.EqvGen.rel 7 6 (by decide))))))
    · exact (Relation.EqvGen.trans 0 1 7 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 7 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 7 (by decide)))))
    · exact (Relation.EqvGen.trans 0 1 8 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 8 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 8 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 7 8 (Relation.EqvGen.rel 5 7 (by decide)) (Relation.EqvGen.rel 7 8 (by decide))))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.rel 0 1 (by decide))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.rel 1 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 7 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.rel 0 1 (by decide))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.rel 1 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 1 5 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 5 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 1 7 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 7 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 7 (by decide)))))
    · exact (Relation.EqvGen.trans 0 1 8 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 8 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 8 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 7 8 (Relation.EqvGen.rel 5 7 (by decide)) (Relation.EqvGen.rel 7 8 (by decide))))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.rel 0 1 (by decide))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.rel 1 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 1 5 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 5 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.rel 0 1 (by decide))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.rel 1 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 1 5 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 5 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 1 7 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 7 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 7 (by decide)))))
    · exact False.elim (hvz rfl)

end WaveTurbulence.Vine
