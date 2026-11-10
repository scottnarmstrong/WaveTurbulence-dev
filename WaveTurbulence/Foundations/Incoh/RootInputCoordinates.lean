/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumTreeInputs

/-! # The finite source root row in the actual leaf-input coordinates

TARGET (incohproof1). This is finite integer typing data, supplied by the
unimodular leaf-coordinate change, with no analytic estimate as a field.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The integer row recovering the root from actual leaf inputs of a couple. -/
structure RootInputCoordinates {n m w : ℕ} (P : MomentumTreeData n m w) where
  sigma : Fin m → ℤ
  abs_sigma_le : ∀ a, |sigma a| ≤ 1
  root_row : (∑ a, sigma a • P.inputRow a) = momentumUnitRow none

/-- Evaluation of the structural integer row gives the literal root momentum relation. -/
theorem RootInputCoordinates.root_eq_sum_inputs {d n m w : ℕ} {P : MomentumTreeData n m w}
    (C : RootInputCoordinates P) (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    k = ∑ a, C.sigma a • P.inputMomentum k x a := by
  have h := congrArg (momentumRowEval (rootLinkMomenta k x)) C.root_row
  simpa only [map_sum, map_zsmul, momentumRowEval_unit, rootLinkMomenta,
    MomentumTreeData.inputMomentum] using h.symm

/-- The row signs have the source real absolute-value bound. -/
theorem RootInputCoordinates.abs_cast_sigma_le {n m w : ℕ} {P : MomentumTreeData n m w}
    (C : RootInputCoordinates P) (a : Fin m) : |(C.sigma a : ℝ)| ≤ 1 := by
  exact_mod_cast C.abs_sigma_le a

end WaveTurbulence.Incoh
