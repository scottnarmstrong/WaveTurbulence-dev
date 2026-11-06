/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
public import WaveTurbulence.Foundations.Molecule.MoleculeDegreeCompat
import Mathlib.Tactic

/-! # C-1 projection from the accepted connected block to its degree data

The source IsVine predicate remains unchanged. Geometric helper results use
only its IsBlockDeg projection, matching the REGRED C-1 adapter.
-/

public section
namespace WaveTurbulence.Vine.Param
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Current source blocks supply the exact legacy geometric degree premises. -/
theorem degreeBlock_of_isBlock (M : Molecule V D) {S : Finset V} {a b : V}
    (hB : M.IsBlock S a b) : M.IsBlockDeg S a b := by
  rcases hB with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,_hc⟩
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

end WaveTurbulence.Vine.Param
