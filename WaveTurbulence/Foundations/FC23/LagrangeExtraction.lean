/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
/-! Real-parameter interpolation for complex-valued polynomial families.
The exact interpolation cost is retained explicitly. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.FC23
open Polynomial Finset

def interpolationNode (D : ℕ) (i : Fin (D + 1)) : ℂ := (i : ℂ) / D

def coefficientCost (D m : ℕ) : ℝ :=
  ∑ i : Fin (D + 1), ‖(Lagrange.basis univ (interpolationNode D) i).coeff m‖

theorem interpolationNode_injective {D : ℕ} (hD : 0 < D) :
    Function.Injective (interpolationNode D) := by
  intro i j h
  have hz : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have h' : (i : ℂ) = (j : ℂ) := (div_left_inj' hz).mp h
  apply Fin.ext
  exact_mod_cast h'

end WaveTurbulence.FC23
