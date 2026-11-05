/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
import Mathlib.Tactic

/-! # Explicit paths avoiding each atom of base template VII -/

public section
namespace WaveTurbulence.Vine

/-- Every surviving base-VII atom reaches the selected surviving root. -/
theorem coreVII_avoid_paths (z v : ℕ) (hz : z<VineType.VII.template.n)
    (hv : v<VineType.VII.template.n) (hvz : v ≠ z) :
    AvoidPath VineType.VII.template.bonds z (if z=0 then 1 else 0) v := by
  change z<11 at hz
  change v<11 at hv
  interval_cases z
  · interval_cases v
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.refl 1)
    · exact (Relation.EqvGen.trans 1 9 2 (Relation.EqvGen.rel 1 9 (by decide)) (Relation.EqvGen.trans 9 7 2 (Relation.EqvGen.rel 9 7 (by decide)) (Relation.EqvGen.rel 7 2 (by decide))))
    · exact (Relation.EqvGen.trans 1 10 3 (Relation.EqvGen.rel 1 10 (by decide)) (Relation.EqvGen.trans 10 8 3 (Relation.EqvGen.rel 10 8 (by decide)) (Relation.EqvGen.rel 8 3 (by decide))))
    · exact (Relation.EqvGen.trans 1 9 4 (Relation.EqvGen.rel 1 9 (by decide)) (Relation.EqvGen.trans 9 7 4 (Relation.EqvGen.rel 9 7 (by decide)) (Relation.EqvGen.trans 7 5 4 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide)))))
    · exact (Relation.EqvGen.trans 1 9 5 (Relation.EqvGen.rel 1 9 (by decide)) (Relation.EqvGen.trans 9 7 5 (Relation.EqvGen.rel 9 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide))))
    · exact (Relation.EqvGen.trans 1 10 6 (Relation.EqvGen.rel 1 10 (by decide)) (Relation.EqvGen.trans 10 8 6 (Relation.EqvGen.rel 10 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide))))
    · exact (Relation.EqvGen.trans 1 9 7 (Relation.EqvGen.rel 1 9 (by decide)) (Relation.EqvGen.rel 9 7 (by decide)))
    · exact (Relation.EqvGen.trans 1 10 8 (Relation.EqvGen.rel 1 10 (by decide)) (Relation.EqvGen.rel 10 8 (by decide)))
    · exact (Relation.EqvGen.rel 1 9 (by decide))
    · exact (Relation.EqvGen.rel 1 10 (by decide))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 4 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 5 4 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 5 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 6 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 3 1 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 1 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 10 1 (Relation.EqvGen.rel 8 10 (by decide)) (Relation.EqvGen.rel 10 1 (by decide)))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 3 4 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 4 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 6 4 (Relation.EqvGen.rel 8 6 (by decide)) (Relation.EqvGen.rel 6 4 (by decide)))))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 5 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 7 5 (Relation.EqvGen.rel 8 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide)))))
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 6 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 7 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 7 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 7 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 9 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 9 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 7 9 (Relation.EqvGen.rel 8 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide)))))
    · exact (Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 1 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 9 1 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 4 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 5 4 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 5 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 6 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 8 6 (Relation.EqvGen.rel 7 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 8 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 8 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 10 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 10 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 8 10 (Relation.EqvGen.rel 7 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 1 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 9 1 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 5 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 6 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 1 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 9 1 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 3 4 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 4 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 6 4 (Relation.EqvGen.rel 8 6 (by decide)) (Relation.EqvGen.rel 6 4 (by decide)))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 6 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 1 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 9 1 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 4 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 5 4 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 5 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 3 1 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 1 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 10 1 (Relation.EqvGen.rel 8 10 (by decide)) (Relation.EqvGen.rel 10 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 3 4 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 4 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 6 4 (Relation.EqvGen.rel 8 6 (by decide)) (Relation.EqvGen.rel 6 4 (by decide)))))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 5 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 6 5 (Relation.EqvGen.rel 8 6 (by decide)) (Relation.EqvGen.rel 6 5 (by decide)))))
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 6 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 9 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 9 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 10 9 (Relation.EqvGen.rel 8 10 (by decide)) (Relation.EqvGen.rel 10 9 (by decide)))))
    · exact (Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 1 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 9 1 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 4 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 5 4 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 5 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 6 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 5 6 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.rel 5 6 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 10 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 10 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 9 10 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 10 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 3 1 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 1 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.trans 8 10 1 (Relation.EqvGen.rel 8 10 (by decide)) (Relation.EqvGen.rel 10 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 4 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 5 4 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 5 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 6 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 1 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 9 1 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 4 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 5 4 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide)))))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 5 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 6 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact False.elim (hvz rfl)

end WaveTurbulence.Vine
