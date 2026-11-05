/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VinePaths

/-! # Explicit paths in the eight pinned templates (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- Every base-template atom is joined to the first joint. -/
theorem template_paths (X : VineType) :
    ∀ v < X.template.n, Relation.EqvGen (EdgeAdj X.template.bonds) 0 v := by
  cases X with
  | I =>
    intro v hv
    norm_num [VineType.template] at hv
    interval_cases v
    · exact Relation.EqvGen.refl 0
    · exact (Relation.EqvGen.rel 0 1 (by decide))
  | II =>
    intro v hv
    norm_num [VineType.template] at hv
    interval_cases v
    · exact Relation.EqvGen.refl 0
    · exact Relation.EqvGen.trans 0 2 1
        (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 1 (by decide))
    · exact Relation.EqvGen.rel 0 2 (by decide)
    · exact Relation.EqvGen.rel 0 3 (by decide)
  | III =>
    intro v hv
    norm_num [VineType.template] at hv
    interval_cases v
    · exact Relation.EqvGen.refl 0
    · exact (Relation.EqvGen.trans 0 7 1 (Relation.EqvGen.trans 0 4 7 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 7 (by decide))) (Relation.EqvGen.rel 7 1 (by decide)))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 4 6 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 6 (by decide)))
    · exact (Relation.EqvGen.trans 0 4 7 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.trans 0 4 6 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 6 (by decide))) (Relation.EqvGen.rel 6 8 (by decide)))
  | IV =>
    intro v hv
    norm_num [VineType.template] at hv
    interval_cases v
    · exact Relation.EqvGen.refl 0
    · exact (Relation.EqvGen.trans 0 7 1 (Relation.EqvGen.trans 0 4 7 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 7 (by decide))) (Relation.EqvGen.rel 7 1 (by decide)))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 4 5 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 6 (by decide)))
    · exact (Relation.EqvGen.trans 0 4 7 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 6 (by decide))) (Relation.EqvGen.rel 6 8 (by decide)))
  | V =>
    intro v hv
    norm_num [VineType.template] at hv
    interval_cases v
    · exact Relation.EqvGen.refl 0
    · exact (Relation.EqvGen.rel 0 1 (by decide))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.rel 1 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.rel 1 3 (by decide))) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 4 6 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 6 (by decide)))
    · exact (Relation.EqvGen.trans 0 5 7 (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.rel 1 3 (by decide))) (Relation.EqvGen.rel 3 5 (by decide))) (Relation.EqvGen.rel 5 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.trans 0 4 6 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 6 (by decide))) (Relation.EqvGen.rel 6 8 (by decide)))
  | VI =>
    intro v hv
    norm_num [VineType.template] at hv
    interval_cases v
    · exact Relation.EqvGen.refl 0
    · exact (Relation.EqvGen.trans 0 13 1 (Relation.EqvGen.trans 0 6 13 (Relation.EqvGen.trans 0 4 6 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 6 (by decide))) (Relation.EqvGen.rel 6 13 (by decide))) (Relation.EqvGen.rel 13 1 (by decide)))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 4 6 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 6 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.trans 0 4 6 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 6 (by decide))) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 5 8 (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))) (Relation.EqvGen.rel 5 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 8 9 (Relation.EqvGen.trans 0 5 8 (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))) (Relation.EqvGen.rel 5 8 (by decide))) (Relation.EqvGen.rel 8 9 (by decide)))
    · exact (Relation.EqvGen.trans 0 8 10 (Relation.EqvGen.trans 0 5 8 (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))) (Relation.EqvGen.rel 5 8 (by decide))) (Relation.EqvGen.rel 8 10 (by decide)))
    · exact (Relation.EqvGen.trans 0 9 11 (Relation.EqvGen.trans 0 8 9 (Relation.EqvGen.trans 0 5 8 (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))) (Relation.EqvGen.rel 5 8 (by decide))) (Relation.EqvGen.rel 8 9 (by decide))) (Relation.EqvGen.rel 9 11 (by decide)))
    · exact (Relation.EqvGen.trans 0 10 12 (Relation.EqvGen.trans 0 8 10 (Relation.EqvGen.trans 0 5 8 (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 5 (by decide))) (Relation.EqvGen.rel 5 8 (by decide))) (Relation.EqvGen.rel 8 10 (by decide))) (Relation.EqvGen.rel 10 12 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 13 (Relation.EqvGen.trans 0 4 6 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 6 (by decide))) (Relation.EqvGen.rel 6 13 (by decide)))
    · exact (Relation.EqvGen.trans 0 7 14 (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.trans 0 4 6 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 6 (by decide))) (Relation.EqvGen.rel 6 7 (by decide))) (Relation.EqvGen.rel 7 14 (by decide)))
  | VII =>
    intro v hv
    norm_num [VineType.template] at hv
    interval_cases v
    · exact Relation.EqvGen.refl 0
    · exact (Relation.EqvGen.trans 0 9 1 (Relation.EqvGen.trans 0 7 9 (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide))) (Relation.EqvGen.rel 7 9 (by decide))) (Relation.EqvGen.rel 9 1 (by decide)))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.rel 0 3 (by decide))
    · exact (Relation.EqvGen.trans 0 5 4 (Relation.EqvGen.trans 0 7 5 (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide))) (Relation.EqvGen.rel 7 5 (by decide))) (Relation.EqvGen.rel 5 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 7 5 (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide))) (Relation.EqvGen.rel 7 5 (by decide)))
    · exact (Relation.EqvGen.trans 0 8 6 (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide))) (Relation.EqvGen.rel 8 6 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 7 9 (Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 7 (by decide))) (Relation.EqvGen.rel 7 9 (by decide)))
    · exact (Relation.EqvGen.trans 0 8 10 (Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.rel 3 8 (by decide))) (Relation.EqvGen.rel 8 10 (by decide)))
  | VIII =>
    intro v hv
    norm_num [VineType.template] at hv
    interval_cases v
    · exact Relation.EqvGen.refl 0
    · exact (Relation.EqvGen.trans 0 4 1 (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide))) (Relation.EqvGen.rel 4 1 (by decide)))
    · exact (Relation.EqvGen.rel 0 2 (by decide))
    · exact (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide)))
    · exact (Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 4 (by decide)))
    · exact (Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.rel 2 3 (by decide))) (Relation.EqvGen.rel 3 5 (by decide)))
    · exact (Relation.EqvGen.rel 0 6 (by decide))
    · exact (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide)))
    · exact (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide)))
    · exact (Relation.EqvGen.trans 0 7 9 (Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 7 (by decide))) (Relation.EqvGen.rel 7 9 (by decide)))
    · exact (Relation.EqvGen.trans 0 8 10 (Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.rel 6 8 (by decide))) (Relation.EqvGen.rel 8 10 (by decide)))

end WaveTurbulence.Vine
