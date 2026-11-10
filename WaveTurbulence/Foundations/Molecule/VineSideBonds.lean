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

end WaveTurbulence.Vine
