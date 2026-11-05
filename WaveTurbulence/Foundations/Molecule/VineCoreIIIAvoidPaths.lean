/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
import Mathlib.Tactic

/-! # Explicit paths avoiding each atom of base template III -/

public section
namespace WaveTurbulence.Vine

/-- Every surviving base-III atom reaches the selected surviving root. -/
theorem coreIII_avoid_paths (z v : ℕ) (hz : z<VineType.III.template.n)
    (hv : v<VineType.III.template.n) (hvz : v ≠ z) :
    AvoidPath VineType.III.template.bonds z (if z=0 then 1 else 0) v := by
  change z<9 at hz
  change v<9 at hv
  interval_cases z
  · interval_cases v
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.refl 1)
    · exact (Relation.EqvGen.trans 1 7 2 (Relation.EqvGen.rel 1 7 (by decide)) (Relation.EqvGen.trans 7 4 2 (Relation.EqvGen.rel 7 4 (by decide)) (Relation.EqvGen.rel 4 2 (by decide))))
    · exact (Relation.EqvGen.trans 1 7 3 (Relation.EqvGen.rel 1 7 (by decide)) (Relation.EqvGen.trans 7 4 3 (Relation.EqvGen.rel 7 4 (by decide)) (Relation.EqvGen.trans 4 5 3 (Relation.EqvGen.rel 4 5 (by decide)) (Relation.EqvGen.rel 5 3 (by decide)))))
    · exact (Relation.EqvGen.trans 1 7 4 (Relation.EqvGen.rel 1 7 (by decide)) (Relation.EqvGen.rel 7 4 (by decide)))
    · exact (Relation.EqvGen.trans 1 7 5 (Relation.EqvGen.rel 1 7 (by decide)) (Relation.EqvGen.trans 7 4 5 (Relation.EqvGen.rel 7 4 (by decide)) (Relation.EqvGen.rel 4 5 (by decide))))
    · exact (Relation.EqvGen.trans 1 8 6 (Relation.EqvGen.rel 1 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide)))
    · exact (Relation.EqvGen.rel 1 7 (by decide))
    · exact (Relation.EqvGen.rel 1 8 (by decide))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 7 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 3 1 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 1 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 4 1 (Relation.EqvGen.rel 5 4 (by decide)) (Relation.EqvGen.trans 4 7 1 (Relation.EqvGen.rel 4 7 (by decide)) (Relation.EqvGen.rel 7 1 (by decide))))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 3 4 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 4 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 6 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 7 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 4 7 (Relation.EqvGen.rel 5 4 (by decide)) (Relation.EqvGen.rel 4 7 (by decide)))))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 8 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 6 8 (Relation.EqvGen.rel 5 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 7 1 (Relation.EqvGen.rel 4 7 (by decide)) (Relation.EqvGen.rel 7 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 5 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 5 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 7 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 3 1 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 1 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 6 1 (Relation.EqvGen.rel 5 6 (by decide)) (Relation.EqvGen.trans 6 8 1 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 1 (by decide))))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 6 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 3 7 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 6 7 (Relation.EqvGen.rel 5 6 (by decide)) (Relation.EqvGen.trans 6 8 7 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 7 (by decide))))))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 8 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 6 8 (Relation.EqvGen.rel 5 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 7 1 (Relation.EqvGen.rel 4 7 (by decide)) (Relation.EqvGen.rel 7 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 7 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 7 1 (Relation.EqvGen.rel 4 7 (by decide)) (Relation.EqvGen.rel 7 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 7 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 7 8 (Relation.EqvGen.rel 4 7 (by decide)) (Relation.EqvGen.rel 7 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 1 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.trans 6 8 1 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.rel 8 1 (by decide))))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact False.elim (hvz rfl)
    · exact (Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
  · interval_cases v
    · exact (Relation.EqvGen.refl 0)
    · exact (Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 7 1 (Relation.EqvGen.rel 4 7 (by decide)) (Relation.EqvGen.rel 7 1 (by decide)))))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide))))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 7 (by decide))))
    · exact False.elim (hvz rfl)

end WaveTurbulence.Vine
