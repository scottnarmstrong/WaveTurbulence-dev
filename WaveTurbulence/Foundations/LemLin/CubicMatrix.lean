/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicDerivative

/-!
# The coefficient matrices of the cubic phase gradients

The coefficients grow at most linearly with `1 + |s| + |t|`. Multiplication
by the gradient preserves the finite family of coordinate-weighted cutoffs.
-/

public section

namespace WaveTurbulence.LemLin

/-- The common stationary scale. -/
@[expose] def cubicScale (s t : ℝ) : ℝ := 1 + |s| + |t|

theorem one_le_cubicScale (s t : ℝ) : 1 ≤ cubicScale s t := by
  unfold cubicScale
  linarith [abs_nonneg s, abs_nonneg t]

theorem cubicScale_pos (s t : ℝ) : 0 < cubicScale s t :=
  lt_of_lt_of_le zero_lt_one (one_le_cubicScale s t)

/-- The symmetric gradient matrix, in the order `x,y,z`. -/
@[expose] def cubicMatrix (kind : CubicPhase) (s t : ℝ) : Fin 3 → Fin 3 → ℝ :=
  match kind with
  | .cross => ![![0, t, s], ![t, 0, 0], ![s, 0, 0]]
  | .collision => ![![0, t, s], ![t, 0, s], ![s, s, -2 * s]]

/-- Each gradient component is a linear combination with this matrix. -/
theorem cubicFrequencyShift_eq_sum (kind : CubicPhase) (s t : ℝ)
    (p : Fin 3 → ℝ) (j : Fin 3) :
    cubicFrequencyShift kind s t p j = ∑ k, cubicMatrix kind s t j k * p k := by
  cases kind <;> fin_cases j <;>
    simp [cubicMatrix, cubicFrequencyShift, Fin.sum_univ_succ]
  ring

/-- A bound uniform over the two phases and all matrix entries. -/
theorem abs_cubicMatrix_le (kind : CubicPhase) (s t : ℝ) (j k : Fin 3) :
    |cubicMatrix kind s t j k| ≤ 2 * cubicScale s t := by
  have hs := abs_nonneg s
  have ht := abs_nonneg t
  cases kind <;> fin_cases j <;> fin_cases k <;>
    simp [cubicMatrix, cubicScale, abs_mul] <;> linarith only [hs, ht]

/-- Multiplying by a coordinate changes only its scalar amplitude. -/
theorem scalarCubicAmplitude_mulCoordinate (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (k : Fin 3) (p : Fin 3 → ℝ) :
    scalarCubicAmplitude kind (Function.update f k (f k).mulCoordinate) s t p =
      (p k : ℂ) * scalarCubicAmplitude kind f s t p := by
  unfold scalarCubicAmplitude
  rw [cubicProduct_update_family]
  have he := cubicProduct_update_family f p k (f k)
  rw [Function.update_eq_self] at he
  rw [he]
  simp only [ScalarCutoff.mulCoordinate]
  ring

/-- Express the gradient contribution using the fixed coordinate-weighted amplitudes. -/
theorem cubicGradient_mul_amplitude (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (j : Fin 3) (p : Fin 3 → ℝ) :
    (cubicFrequencyShift kind s t p j : ℂ) * scalarCubicAmplitude kind f s t p =
      ∑ k, (cubicMatrix kind s t j k : ℂ) *
        scalarCubicAmplitude kind (Function.update f k (f k).mulCoordinate) s t p := by
  rw [cubicFrequencyShift_eq_sum]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [scalarCubicAmplitude_mulCoordinate]
  ring

end WaveTurbulence.LemLin
