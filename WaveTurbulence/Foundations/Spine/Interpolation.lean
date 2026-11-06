/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! TARGET L2220–2227: interpolation of the two independent spliced-kernel estimates. -/
public section
namespace WaveTurbulence.LGSpine

theorem norm_le_interpolation {z : ℂ} {A B aWeight : ℝ} (hA : ‖z‖ ≤ A) (hB : ‖z‖ ≤ B)
    (haWeight0 : 0 ≤ aWeight) (haWeight1 : aWeight ≤ 1) : ‖z‖ ≤ A ^ aWeight * B ^ (1 - aWeight) := by
  have hA0 := (norm_nonneg z).trans hA
  have hB0 := (norm_nonneg z).trans hB
  by_cases hz : z = 0
  · rw [hz, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _)
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc
      ‖z‖ = ‖z‖ ^ aWeight * ‖z‖ ^ (1 - aWeight) := by
        rw [← Real.rpow_add hn, show aWeight + (1 - aWeight) = 1 by ring, Real.rpow_one]
      _ ≤ _ := mul_le_mul (Real.rpow_le_rpow hn.le hA haWeight0)
        (Real.rpow_le_rpow hn.le hB (sub_nonneg.mpr haWeight1))
        (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg hA0 _)

theorem norm_le_exp_interpolation {z : ℂ} {a b aWeight : ℝ}
    (ha : ‖z‖ ≤ Real.exp a) (hb : ‖z‖ ≤ Real.exp b) (haWeight0 : 0 ≤ aWeight) (haWeight1 : aWeight ≤ 1) :
    ‖z‖ ≤ Real.exp (aWeight * a + (1 - aWeight) * b) := by
  have h := norm_le_interpolation ha hb haWeight0 haWeight1
  simpa only [← Real.exp_mul, ← Real.exp_add, mul_comm a aWeight, mul_comm b (1 - aWeight)] using h

end WaveTurbulence.LGSpine
