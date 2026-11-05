/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VinePaths
public import WaveTurbulence.Foundations.Molecule.VineTemplates
import Mathlib.Tactic

/-! # Literal single-bond backbones of the base templates -/

public section
namespace WaveTurbulence.Vine

/-- Keep encoded bonds whose unordered multiplicity is exactly one. -/
@[expose] def singleBonds (es : List (ℕ×ℕ)) : List (ℕ×ℕ) :=
  es.filter fun e => es.count e+es.count (e.2,e.1)=1

/-- The type-II single bonds join every noncentral atom to joint zero. -/
theorem coreII_single_backbone (v : ℕ) (hv : v<4) :
    Relation.EqvGen (EdgeAdj (singleBonds VineType.II.template.bonds)) 0 v := by
  interval_cases v
  · exact Relation.EqvGen.refl 0
  · exact Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) ((Relation.EqvGen.rel 2 1 (by decide)))
  · exact (Relation.EqvGen.rel 0 2 (by decide))
  · exact (Relation.EqvGen.rel 0 3 (by decide))

/-- The type-III single bonds join every noncentral atom to joint zero. -/
theorem coreIII_single_backbone (v : ℕ) (hv : v<9) :
    Relation.EqvGen (EdgeAdj (singleBonds VineType.III.template.bonds)) 0 v := by
  interval_cases v
  · exact Relation.EqvGen.refl 0
  · exact Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 7 1 (Relation.EqvGen.rel 4 7 (by decide)) ((Relation.EqvGen.rel 7 1 (by decide)))))
  · exact (Relation.EqvGen.rel 0 2 (by decide))
  · exact (Relation.EqvGen.rel 0 3 (by decide))
  · exact Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) ((Relation.EqvGen.rel 2 4 (by decide)))
  · exact Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) ((Relation.EqvGen.rel 3 5 (by decide)))
  · exact Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) ((Relation.EqvGen.rel 4 6 (by decide))))
  · exact Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) ((Relation.EqvGen.rel 4 7 (by decide))))
  · exact Relation.EqvGen.trans 0 2 8 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 8 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 8 (Relation.EqvGen.rel 4 6 (by decide)) ((Relation.EqvGen.rel 6 8 (by decide)))))

/-- The type-IV single bonds join every noncentral atom to joint zero. -/
theorem coreIV_single_backbone (v : ℕ) (hv : v<9) (hne : v ≠ 5) :
    Relation.EqvGen (EdgeAdj (singleBonds VineType.IV.template.bonds)) 0 v := by
  interval_cases v
  · exact Relation.EqvGen.refl 0
  · exact Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 7 1 (Relation.EqvGen.rel 4 7 (by decide)) ((Relation.EqvGen.rel 7 1 (by decide)))))
  · exact (Relation.EqvGen.rel 0 2 (by decide))
  · exact (Relation.EqvGen.rel 0 3 (by decide))
  · exact Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) ((Relation.EqvGen.rel 2 4 (by decide)))
  · exact False.elim (hne rfl)
  · exact Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) ((Relation.EqvGen.rel 3 6 (by decide)))
  · exact Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) ((Relation.EqvGen.rel 4 7 (by decide))))
  · exact Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 6 8 (Relation.EqvGen.rel 3 6 (by decide)) ((Relation.EqvGen.rel 6 8 (by decide))))

/-- The type-V single bonds join every noncentral atom to joint zero. -/
theorem coreV_single_backbone (v : ℕ) (hv : v<9) (hne : v ≠ 8) :
    Relation.EqvGen (EdgeAdj (singleBonds VineType.V.template.bonds)) 0 v := by
  interval_cases v
  · exact Relation.EqvGen.refl 0
  · exact (Relation.EqvGen.rel 0 1 (by decide))
  · exact (Relation.EqvGen.rel 0 2 (by decide))
  · exact Relation.EqvGen.trans 0 1 3 (Relation.EqvGen.rel 0 1 (by decide)) ((Relation.EqvGen.rel 1 3 (by decide)))
  · exact Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) ((Relation.EqvGen.rel 2 4 (by decide)))
  · exact Relation.EqvGen.trans 0 1 5 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 5 (Relation.EqvGen.rel 1 3 (by decide)) ((Relation.EqvGen.rel 3 5 (by decide))))
  · exact Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) ((Relation.EqvGen.rel 4 6 (by decide))))
  · exact Relation.EqvGen.trans 0 1 7 (Relation.EqvGen.rel 0 1 (by decide)) (Relation.EqvGen.trans 1 3 7 (Relation.EqvGen.rel 1 3 (by decide)) (Relation.EqvGen.trans 3 5 7 (Relation.EqvGen.rel 3 5 (by decide)) ((Relation.EqvGen.rel 5 7 (by decide)))))
  · exact False.elim (hne rfl)

/-- The type-VI single bonds join every noncentral atom to joint zero. -/
theorem coreVI_single_backbone (v : ℕ) (hv : v<15) (hne : v ≠ 12) :
    Relation.EqvGen (EdgeAdj (singleBonds VineType.VI.template.bonds)) 0 v := by
  interval_cases v
  · exact Relation.EqvGen.refl 0
  · exact Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 1 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.trans 6 13 1 (Relation.EqvGen.rel 6 13 (by decide)) ((Relation.EqvGen.rel 13 1 (by decide))))))
  · exact (Relation.EqvGen.rel 0 2 (by decide))
  · exact (Relation.EqvGen.rel 0 3 (by decide))
  · exact Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) ((Relation.EqvGen.rel 2 4 (by decide)))
  · exact Relation.EqvGen.trans 0 3 5 (Relation.EqvGen.rel 0 3 (by decide)) ((Relation.EqvGen.rel 3 5 (by decide)))
  · exact Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) ((Relation.EqvGen.rel 4 6 (by decide))))
  · exact Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 7 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.trans 6 13 7 (Relation.EqvGen.rel 6 13 (by decide)) (Relation.EqvGen.trans 13 1 7 (Relation.EqvGen.rel 13 1 (by decide)) (Relation.EqvGen.trans 1 14 7 (Relation.EqvGen.rel 1 14 (by decide)) ((Relation.EqvGen.rel 14 7 (by decide))))))))
  · exact Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 8 (Relation.EqvGen.rel 3 5 (by decide)) ((Relation.EqvGen.rel 5 8 (by decide))))
  · exact Relation.EqvGen.trans 0 3 9 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 9 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 8 9 (Relation.EqvGen.rel 5 8 (by decide)) (Relation.EqvGen.trans 8 10 9 (Relation.EqvGen.rel 8 10 (by decide)) (Relation.EqvGen.trans 10 11 9 (Relation.EqvGen.rel 10 11 (by decide)) ((Relation.EqvGen.rel 11 9 (by decide)))))))
  · exact Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 10 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 8 10 (Relation.EqvGen.rel 5 8 (by decide)) ((Relation.EqvGen.rel 8 10 (by decide)))))
  · exact Relation.EqvGen.trans 0 3 11 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 5 11 (Relation.EqvGen.rel 3 5 (by decide)) (Relation.EqvGen.trans 5 8 11 (Relation.EqvGen.rel 5 8 (by decide)) (Relation.EqvGen.trans 8 10 11 (Relation.EqvGen.rel 8 10 (by decide)) ((Relation.EqvGen.rel 10 11 (by decide))))))
  · exact False.elim (hne rfl)
  · exact Relation.EqvGen.trans 0 2 13 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 13 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 13 (Relation.EqvGen.rel 4 6 (by decide)) ((Relation.EqvGen.rel 6 13 (by decide)))))
  · exact Relation.EqvGen.trans 0 2 14 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 14 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 14 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.trans 6 13 14 (Relation.EqvGen.rel 6 13 (by decide)) (Relation.EqvGen.trans 13 1 14 (Relation.EqvGen.rel 13 1 (by decide)) ((Relation.EqvGen.rel 1 14 (by decide)))))))

/-- The type-VII single bonds join every noncentral atom to joint zero. -/
theorem coreVII_single_backbone (v : ℕ) (hv : v<11) (hne : v ≠ 4) :
    Relation.EqvGen (EdgeAdj (singleBonds VineType.VII.template.bonds)) 0 v := by
  interval_cases v
  · exact Relation.EqvGen.refl 0
  · exact Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 1 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 9 1 (Relation.EqvGen.rel 7 9 (by decide)) ((Relation.EqvGen.rel 9 1 (by decide)))))
  · exact (Relation.EqvGen.rel 0 2 (by decide))
  · exact (Relation.EqvGen.rel 0 3 (by decide))
  · exact False.elim (hne rfl)
  · exact Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 5 (Relation.EqvGen.rel 2 7 (by decide)) ((Relation.EqvGen.rel 7 5 (by decide))))
  · exact Relation.EqvGen.trans 0 3 6 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 6 (Relation.EqvGen.rel 3 8 (by decide)) ((Relation.EqvGen.rel 8 6 (by decide))))
  · exact Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) ((Relation.EqvGen.rel 2 7 (by decide)))
  · exact Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) ((Relation.EqvGen.rel 3 8 (by decide)))
  · exact Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) ((Relation.EqvGen.rel 7 9 (by decide))))
  · exact Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) ((Relation.EqvGen.rel 8 10 (by decide))))

/-- The type-VIII single bonds join every noncentral atom to joint zero. -/
theorem coreVIII_single_backbone (v : ℕ) (hv : v<11) (hne : v ≠ 10) :
    Relation.EqvGen (EdgeAdj (singleBonds VineType.VIII.template.bonds)) 0 v := by
  interval_cases v
  · exact Relation.EqvGen.refl 0
  · exact Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) ((Relation.EqvGen.rel 4 1 (by decide))))
  · exact (Relation.EqvGen.rel 0 2 (by decide))
  · exact Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 3 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 1 3 (Relation.EqvGen.rel 4 1 (by decide)) (Relation.EqvGen.trans 1 5 3 (Relation.EqvGen.rel 1 5 (by decide)) ((Relation.EqvGen.rel 5 3 (by decide))))))
  · exact Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) ((Relation.EqvGen.rel 2 4 (by decide)))
  · exact Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 5 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 1 5 (Relation.EqvGen.rel 4 1 (by decide)) ((Relation.EqvGen.rel 1 5 (by decide)))))
  · exact (Relation.EqvGen.rel 0 6 (by decide))
  · exact Relation.EqvGen.trans 0 6 7 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 7 (Relation.EqvGen.rel 6 8 (by decide)) (Relation.EqvGen.trans 8 9 7 (Relation.EqvGen.rel 8 9 (by decide)) ((Relation.EqvGen.rel 9 7 (by decide)))))
  · exact Relation.EqvGen.trans 0 6 8 (Relation.EqvGen.rel 0 6 (by decide)) ((Relation.EqvGen.rel 6 8 (by decide)))
  · exact Relation.EqvGen.trans 0 6 9 (Relation.EqvGen.rel 0 6 (by decide)) (Relation.EqvGen.trans 6 8 9 (Relation.EqvGen.rel 6 8 (by decide)) ((Relation.EqvGen.rel 8 9 (by decide))))
  · exact False.elim (hne rfl)

end WaveTurbulence.Vine
