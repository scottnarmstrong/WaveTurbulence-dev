/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
import Mathlib.Tactic

/-! # Explicit paths avoiding each atom of base template VIII -/

public section
namespace WaveTurbulence.Vine

/-- Every surviving base-VIII atom reaches the selected surviving root. -/
theorem coreVIII_avoid_paths (z v : ℕ) (hz : z<VineType.VIII.template.n)
    (hv : v<VineType.VIII.template.n) (hvz : v ≠ z) :
    AvoidPath VineType.VIII.template.bonds z (if z=0 then 1 else 0) v := by
  change z<11 at hz
  change v<11 at hv
  interval_cases z
  · interval_cases v
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.refl 1)
    · exact (Relation.EqvGen.trans 1 4 2 (Relation.EqvGen.rel 1 4 (by decide)) (Relation.EqvGen.rel 4 2 (by decide)))
    · exact (Relation.EqvGen.trans 1 5 3 (Relation.EqvGen.rel 1 5 (by decide)) (Relation.EqvGen.rel 5 3 (by decide)))
    · exact (Relation.EqvGen.rel 1 4 (by decide))
    · exact (Relation.EqvGen.rel 1 5 (by decide))
    · exact (Relation.EqvGen.trans 1 5 6 (Relation.EqvGen.rel 1 5 (by decide)) (Relation.EqvGen.trans 5 3 6 (Relation.EqvGen.rel 5 3 (by decide)) (Relation.EqvGen.trans 3 7 6 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.rel 7 6 (by decide)))))
    · exact (Relation.EqvGen.trans 1 5 7 (Relation.EqvGen.rel 1 5 (by decide)) (Relation.EqvGen.trans 5 3 7 (Relation.EqvGen.rel 5 3 (by decide)) (Relation.EqvGen.rel 3 7 (by decide))))
    · exact (Relation.EqvGen.trans 1 5 8 (Relation.EqvGen.rel 1 5 (by decide)) (Relation.EqvGen.trans 5 3 8 (Relation.EqvGen.rel 5 3 (by decide)) (Relation.EqvGen.trans 3 7 8 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.trans 7 6 8 (Relation.EqvGen.rel 7 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide))))))
    · exact (Relation.EqvGen.trans 1 5 9 (Relation.EqvGen.rel 1 5 (by decide)) (Relation.EqvGen.trans 5 3 9 (Relation.EqvGen.rel 5 3 (by decide)) (Relation.EqvGen.trans 3 7 9 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide)))))
    · exact (Relation.EqvGen.trans 1 5 10 (Relation.EqvGen.rel 1 5 (by decide)) (Relation.EqvGen.trans 5 3 10 (Relation.EqvGen.rel 5 3 (by decide)) (Relation.EqvGen.trans 3 7 10 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.trans 7 9 10 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 10 (by decide))))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 9 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 9 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 6 10 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 10 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 6 1 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 1 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.trans 7 3 1 (Relation.EqvGen.rel 7 3 (by decide)) (Relation.EqvGen.trans 3 5 1 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 1 (by decide))))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 6 3 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 3 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.rel 7 3 (by decide))))
    · exact (Relation.EqvGen.trans 0 6 4 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 4 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.trans 7 3 4 (Relation.EqvGen.rel 7 3 (by decide)) (Relation.EqvGen.trans 3 5 4 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide))))))
    · exact (Relation.EqvGen.trans 0 6 5 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 5 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.trans 7 3 5 (Relation.EqvGen.rel 7 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))))
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 9 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 9 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 6 10 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 10 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 1 (by decide))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 5 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 5 (by decide))))
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 9 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 9 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 6 10 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 10 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 1 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 5 1 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 9 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 9 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 6 10 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 10 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 1 (by decide))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 9 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 9 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 6 10 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 10 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 1 (by decide))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 7 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 7 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 8 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 7 8 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.trans 7 9 8 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 8 (by decide))))))
    · exact (Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 9 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 7 9 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 10 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 10 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 7 10 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.trans 7 9 10 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 10 (by decide))))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 1 (by decide))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 9 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 9 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 6 10 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 10 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 1 (by decide))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 6 9 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 9 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 6 10 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 10 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.trans 7 9 10 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 10 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 1 (by decide))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 6 10 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 10 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 1 (by decide))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))))
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 9 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 7 9 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact False.elim (hvz rfl)

end WaveTurbulence.Vine
