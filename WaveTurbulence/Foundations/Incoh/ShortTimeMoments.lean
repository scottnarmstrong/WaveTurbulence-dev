/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.BracketIntegrability

/-!
# Finite short-time profile moments

TARGET (incohproof14)–(incohproof15): the first moment of `⟨s⟩⁻ᵈ` is
finite for `d ≥ 3`, the precise dimension threshold used in the separated boxes.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- The first moment loses only one power of the Japanese bracket. -/
theorem abs_mul_inverseBracketPower_le (q s : ℝ) :
    |s| * Fourier.inverseBracketPower q s ≤ Fourier.inverseBracketPower (q - 1) s := by
  have hp : 0 < Real.sqrt (1 + s ^ 2) := by positivity
  have hs : |s| ≤ Real.sqrt (1 + s ^ 2) := by
    rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
    simp only [sq_abs]
    linarith
  calc
    _ ≤ Real.sqrt (1 + s ^ 2) * Fourier.inverseBracketPower q s :=
      mul_le_mul_of_nonneg_right hs (Fourier.inverseBracketPower_nonneg _ _)
    _ = _ := by
      unfold Fourier.inverseBracketPower
      calc
        _ = Real.sqrt (1 + s ^ 2) ^ (1 : ℝ) * Real.sqrt (1 + s ^ 2) ^ (-q) := by rw [Real.rpow_one]
        _ = Real.sqrt (1 + s ^ 2) ^ (1 + -q) := (Real.rpow_add hp _ _).symm
        _ = _ := by congr 1; ring

/-- The first moment required by incoherence is an actual integrable function. -/
theorem integrable_firstMoment_inverseBracketPower {q : ℝ} (hq : 2 < q) :
    Integrable (fun s : ℝ => |s| * Fourier.inverseBracketPower q s) := by
  have hi := Fourier.integrable_inverseBracketPower (by linarith : 1 < q - 1)
  have hc : Continuous (fun s : ℝ => |s| * Fourier.inverseBracketPower q s) := by
    apply continuous_abs.mul
    unfold Fourier.inverseBracketPower
    exact (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))).rpow_const
      (fun s => Or.inl (ne_of_gt (Real.sqrt_pos_of_pos (by change 0 < 1 + s ^ 2; positivity))))
  apply hi.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Fourier.inverseBracketPower_nonneg _ _))]
    exact abs_mul_inverseBracketPower_le q s

end WaveTurbulence.Incoh
