/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInteriorPaths
import Mathlib.Tactic

/-! # Explicit paths connecting every base vine nonjoint atom -/

public section
namespace WaveTurbulence.Vine

/-- All nonjoint atoms of every base template are connected within that interior. -/
theorem template_interior_connected (X : VineType) : InteriorConnected X.template := by
  cases X with
  | I =>
    intro v hv hvn
    change v<2 at hvn
    omega
  | II =>
    intro v hv hvn
    change v<4 at hvn
    interval_cases v
    · exact (Relation.EqvGen.refl 2)
    · exact (Relation.EqvGen.rel 2 3 (by decide))
  | III =>
    intro v hv hvn
    change v<9 at hvn
    interval_cases v
    · exact (Relation.EqvGen.refl 2)
    · exact (Relation.EqvGen.rel 2 3 (by decide))
    · exact (Relation.EqvGen.rel 2 4 (by decide))
    · exact (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide)))
    · exact (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 7 (by decide)))
    · exact (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide))))
  | IV =>
    intro v hv hvn
    change v<9 at hvn
    interval_cases v
    · exact (Relation.EqvGen.refl 2)
    · exact (Relation.EqvGen.rel 2 3 (by decide))
    · exact (Relation.EqvGen.rel 2 4 (by decide))
    · exact (Relation.EqvGen.trans 2 4 5 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 5 (by decide)))
    · exact (Relation.EqvGen.trans 2 3 6 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 6 (by decide)))
    · exact (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 7 (by decide)))
    · exact (Relation.EqvGen.trans 2 3 8 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 6 8 (Relation.EqvGen.rel 3 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide))))
  | V =>
    intro v hv hvn
    change v<9 at hvn
    interval_cases v
    · exact (Relation.EqvGen.refl 2)
    · exact (Relation.EqvGen.rel 2 3 (by decide))
    · exact (Relation.EqvGen.rel 2 4 (by decide))
    · exact (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide)))
    · exact (Relation.EqvGen.trans 2 3 7 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 7 (by decide))))
    · exact (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide))))
  | VI =>
    intro v hv hvn
    change v<15 at hvn
    interval_cases v
    · exact (Relation.EqvGen.refl 2)
    · exact (Relation.EqvGen.rel 2 3 (by decide))
    · exact (Relation.EqvGen.rel 2 4 (by decide))
    · exact (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.rel 4 6 (by decide)))
    · exact (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 7 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide))))
    · exact (Relation.EqvGen.trans 2 3 8 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 5 8 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.rel 5 8 (by decide))))
    · exact (Relation.EqvGen.trans 2 3 9 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 5 9 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 8 9 (Relation.EqvGen.rel 5 8 (by decide)) (Relation.EqvGen.rel 8 9 (by decide)))))
    · exact (Relation.EqvGen.trans 2 3 10 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 5 10 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 8 10 (Relation.EqvGen.rel 5 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide)))))
    · exact (Relation.EqvGen.trans 2 3 11 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 5 11 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 8 11 (Relation.EqvGen.rel 5 8 (by decide)) (Relation.EqvGen.trans 8 9 11 (Relation.EqvGen.rel 8 9 (by decide)) (Relation.EqvGen.rel 9 11 (by decide))))))
    · exact (Relation.EqvGen.trans 2 3 12 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 5 12 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 8 12 (Relation.EqvGen.rel 5 8 (by decide)) (Relation.EqvGen.trans 8 10 12 (Relation.EqvGen.rel 8 10 (by decide)) (Relation.EqvGen.rel 10 12 (by decide))))))
    · exact (Relation.EqvGen.trans 2 4 13 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 13 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.rel 6 13 (by decide))))
    · exact (Relation.EqvGen.trans 2 4 14 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 14 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.trans 6 7 14 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.rel 7 14 (by decide)))))
  | VII =>
    intro v hv hvn
    change v<11 at hvn
    interval_cases v
    · exact (Relation.EqvGen.refl 2)
    · exact (Relation.EqvGen.rel 2 3 (by decide))
    · exact (Relation.EqvGen.trans 2 7 4 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 5 4 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.rel 5 4 (by decide))))
    · exact (Relation.EqvGen.trans 2 7 5 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 5 (by decide)))
    · exact (Relation.EqvGen.trans 2 3 6 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 8 6 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 6 (by decide))))
    · exact (Relation.EqvGen.rel 2 7 (by decide))
    · exact (Relation.EqvGen.trans 2 3 8 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide)))
    · exact (Relation.EqvGen.trans 2 3 10 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) (Relation.EqvGen.rel 8 10 (by decide))))
  | VIII =>
    intro v hv hvn
    change v<11 at hvn
    interval_cases v
    · exact (Relation.EqvGen.refl 2)
    · exact (Relation.EqvGen.rel 2 3 (by decide))
    · exact (Relation.EqvGen.rel 2 4 (by decide))
    · exact (Relation.EqvGen.trans 2 3 5 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 2 3 6 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 7 6 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.rel 7 6 (by decide))))
    · exact (Relation.EqvGen.trans 2 3 7 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.rel 3 7 (by decide)))
    · exact (Relation.EqvGen.trans 2 3 8 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 7 8 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.trans 7 6 8 (Relation.EqvGen.rel 7 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))))
    · exact (Relation.EqvGen.trans 2 3 9 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 7 9 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.rel 7 9 (by decide))))
    · exact (Relation.EqvGen.trans 2 3 10 (Relation.EqvGen.rel 2 3 (by decide)) (Relation.EqvGen.trans 3 7 10 (Relation.EqvGen.rel 3 7 (by decide)) (Relation.EqvGen.trans 7 9 10 (Relation.EqvGen.rel 7 9 (by decide)) (Relation.EqvGen.rel 9 10 (by decide)))))

end WaveTurbulence.Vine
