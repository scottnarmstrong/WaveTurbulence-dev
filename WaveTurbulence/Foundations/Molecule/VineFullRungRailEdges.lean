/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungSequences

/-! # Actual rail edges recorded by full-rung incidence rows -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*}

/-- The predecessor rail edge is one of the actual four recorded darts. -/
theorem FullRungSequence.upper_prev_adj {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : M.Adj (Q.u i) (Q.u (i-1)) :=
  ⟨(Q.upper i hi hin).dart 2,(Q.upper i hi hin).atom_eq 2,(Q.upper i hi hin).neighbor_eq 2⟩

/-- The successor rail edge is one of the actual four recorded darts. -/
theorem FullRungSequence.upper_next_adj {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : M.Adj (Q.u i) (Q.u (i+1)) :=
  ⟨(Q.upper i hi hin).dart 3,(Q.upper i hi hin).atom_eq 3,(Q.upper i hi hin).neighbor_eq 3⟩

/-- The lower predecessor rail edge is also an actual incidence. -/
theorem FullRungSequence.lower_prev_adj {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : M.Adj (Q.v i) (Q.v (i-1)) :=
  ⟨(Q.lower i hi hin).dart 2,(Q.lower i hi hin).atom_eq 2,(Q.lower i hi hin).neighbor_eq 2⟩

/-- The lower successor rail edge is also an actual incidence. -/
theorem FullRungSequence.lower_next_adj {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : M.Adj (Q.v i) (Q.v (i+1)) :=
  ⟨(Q.lower i hi hin).dart 3,(Q.lower i hi hin).atom_eq 3,(Q.lower i hi hin).neighbor_eq 3⟩

end WaveTurbulence.Vine
