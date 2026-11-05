/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRawCuts
public import WaveTurbulence.Foundations.Molecule.VineMaskedDegrees
import Mathlib.Tactic

/-! # Linear binary-mask coordinates for finite core cut certificates -/

public section
namespace WaveTurbulence.Vine

/-- Absolute differences of binary atom memberships count raw crossing
bonds, with both occurrences retained for a doubled edge. -/
@[expose] def binaryCut (b : ℕ → ℕ) (es : List (ℕ×ℕ)) : ℕ :=
  (es.map (fun p => (b p.1-b p.2)+(b p.2-b p.1))).sum

/-- The arithmetic mask formula agrees with the literal cut on every list. -/
theorem rawCut_eq_binaryCut (W : Finset ℕ) (es : List (ℕ×ℕ)) :
    rawCut W es=binaryCut (membershipMask W) es := by
  unfold rawCut binaryCut
  congr 1
  apply List.map_congr_left
  intro p _hp
  by_cases h1 : p.1 ∈ W <;> by_cases h2 : p.2 ∈ W <;>
    simp [cutWeight_pair,membershipMask,h1,h2]

/-- Absolute difference dominates both directed differences, as a pair
of linear inequalities. This avoids introducing subtraction case splits
inside the larger finite-core arithmetic certificates. -/
theorem binaryCut_edge_bounds (b : ℕ → ℕ) (a d : ℕ) :
    b a ≤ b d+((b a-b d)+(b d-b a)) ∧
      b d ≤ b a+((b a-b d)+(b d-b a)) := by omega

end WaveTurbulence.Vine
