/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungNeighbors
public import WaveTurbulence.Foundations.Molecule.VineInsertionCounts
import Mathlib.Tactic

/-! # The exact edge list of the triangular side and its full-rung ladder -/

public section
namespace WaveTurbulence.Vine

/-- Two doubled triangular sides, its third single side, the direct
joint bond, and k full rungs with their two rails. Labels N..N+2k-1 are fresh. -/
@[expose] def sideBonds (N k : ℕ) : List (ℕ×ℕ) :=
  [(4,5),(4,5),(4,6),(4,6),(5,6),(7,8)] ++
    railBonds 5 ((List.range k).map (N+·)) 7 ++
    railBonds 6 ((List.range k).map (N+k+·)) 8 ++ allocatedRungs N (N+k) k

/-- Each full rung contributes its two parallel bonds to the literal list. -/
theorem allocatedRungs_length (N P k : ℕ) : (allocatedRungs N P k).length=2*k := by
  induction k generalizing N P with
  | zero => rfl
  | succ k ih =>
    rw [allocatedRungs_succ]
    simp only [List.length_cons,ih]
    omega

/-- The full side has exactly8+4k bonds, agreeing with E+2=2V. -/
theorem sideBonds_length (N k : ℕ) : (sideBonds N k).length=8+4*k := by
  simp only [sideBonds,List.length_append,List.length_cons,List.length_nil,
    railBonds_length,List.length_map,List.length_range,allocatedRungs_length]
  omega

end WaveTurbulence.Vine
