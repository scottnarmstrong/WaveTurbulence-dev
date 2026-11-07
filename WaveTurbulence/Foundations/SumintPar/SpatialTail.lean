/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.WeightBounds
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Integrable spatial tails for sumint weight localization

The exact draft Japanese bracket has integrable inverse integer powers
when the power exceeds dimension. This will sum the localized ℒ¹ Fourier
bounds of the decaying 𝒦 weights over all centers.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

/-- The spatial majorant furnished by the draft S norm. -/
@[expose] noncomputable def inverseSpatialWeight {d : ℕ} (K : ℕ) (x : Mom d) : ℝ :=
  1 / jbr x ^ K

/-- Nonnegativity of the spatial majorant. -/
theorem inverseSpatialWeight_nonneg {d : ℕ} (K : ℕ) (x : Mom d) :
    0 ≤ inverseSpatialWeight K x := by
  exact div_nonneg (by norm_num) (pow_nonneg (le_trans (by norm_num) (one_le_jbr x)) K)

/-- Rewrite the integer bracket power into Mathlib's integrable rpow form. -/
theorem inverseSpatialWeight_eq {d : ℕ} (K : ℕ) (x : Mom d) :
    inverseSpatialWeight K x = (1 + ‖x‖ ^ 2) ^ (-(K : ℝ) / 2) := by
  unfold inverseSpatialWeight jbr
  have hb : 0 ≤ 1 + ‖x‖ ^ 2 := by positivity
  calc
    _ = (Real.sqrt (1 + ‖x‖ ^ 2)) ^ (-(K : ℝ)) := by
      rw [Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast, one_div]
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hb]
      congr 1
      ring

/-- The source exponent `30d` has more than the required integrability margin. -/
theorem integrable_inverseSpatialWeight {d K : ℕ} (hK : d < K) :
    Integrable (inverseSpatialWeight (d := d) K) := by
  have hn : (Module.finrank ℝ (Mom d) : ℝ) < (K : ℝ) := by
    simpa [Mom] using (show (d : ℝ) < (K : ℝ) by exact_mod_cast hK)
  have hi := integrable_rpow_neg_one_add_norm_sq (E := Mom d) (μ := volume) (r := (K : ℝ)) hn
  simpa only [← inverseSpatialWeight_eq] using hi

end WaveTurbulence.SumintPar
