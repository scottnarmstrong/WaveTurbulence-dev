/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Coordinate rotations of the planar integer lattice

The three nontrivial quarter-turn rotations used to reduce all four Cartesian
annulus charts to the upper chart. These are exact injective integer maps.
-/

public section

namespace WaveTurbulence.Counting

/-- Rotation of integer coordinates through a quarter turn. -/
@[expose] def latticeQuarterTurn : (Fin 2 → ℤ) ↪ (Fin 2 → ℤ) where
  toFun n := ![-n 1,n 0]
  inj' := by
    intro x y h
    have h0 : x 0 = y 0 := congrFun h 1
    have h1 : -x 1 = -y 1 := congrFun h 0
    ext i
    fin_cases i
    · exact h0
    · exact neg_injective h1

/-- Rotation of integer coordinates through a half turn. -/
@[expose] def latticeHalfTurn : (Fin 2 → ℤ) ↪ (Fin 2 → ℤ) where
  toFun n := ![-n 0,-n 1]
  inj' := by
    intro x y h
    have h0 : -x 0 = -y 0 := congrFun h 0
    have h1 : -x 1 = -y 1 := congrFun h 1
    ext i
    fin_cases i
    · exact neg_injective h0
    · exact neg_injective h1

/-- Rotation of integer coordinates through three quarter turns. -/
@[expose] def latticeThreeQuarterTurn : (Fin 2 → ℤ) ↪ (Fin 2 → ℤ) where
  toFun n := ![n 1,-n 0]
  inj' := by
    intro x y h
    have h0 : -x 0 = -y 0 := congrFun h 1
    have h1 : x 1 = y 1 := congrFun h 0
    ext i
    fin_cases i
    · exact neg_injective h0
    · exact h1

end WaveTurbulence.Counting
