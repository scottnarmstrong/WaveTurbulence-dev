/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialInputBounds

/-!
# Decay in localization centers from the literal source spatial norm

A fixed-radius momentum cell transfers the source Japanese-bracket decay
to its center. Constants depend only on the fixed radius and derivative order.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The Japanese bracket is positive and bounded below by one. -/
theorem one_le_momentumBracket {d : ℕ} (x : Mom d) : 1 ≤ Fourier.momentumBracket x := by
  unfold Fourier.momentumBracket
  exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg ‖x‖])

/-- Brackets at two points in a fixed-radius cell are uniformly comparable. -/
theorem momentumBracket_center_le {d : ℕ} {R : ℝ} (hR : 0 ≤ R) {c x : Mom d}
    (hx : ‖x - c‖ ≤ R) : Fourier.momentumBracket c ≤ (2 + R) * Fourier.momentumBracket x := by
  have hbx := one_le_momentumBracket x
  have hnx : ‖x‖ ≤ Fourier.momentumBracket x := by
    unfold Fourier.momentumBracket
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by linarith)
  have hnc : ‖c‖ ≤ ‖x‖ + R := by
    have h := norm_add_le x (c - x)
    rw [add_sub_cancel, norm_sub_rev] at h
    exact h.trans (add_le_add le_rfl hx)
  have hbc : Fourier.momentumBracket c ≤ 1 + ‖c‖ := by
    unfold Fourier.momentumBracket
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [norm_nonneg c]
  have hr := mul_le_mul_of_nonneg_left hbx hR
  nlinarith only [hbc, hnc, hnx, hbx, hr]

/-- Derivatives on a localization cell carry summable decay in its center. -/
theorem norm_iteratedFDeriv_le_center_decay {d K M j : ℕ} {f : Mom d → ℂ} {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B)
    (hj : j ≤ K) {c x : Mom d} (hx : ‖x - c‖ ≤ R) :
    ‖iteratedFDeriv ℝ j f x‖ ≤
      (d : ℝ) ^ j * (B * (2 + R) ^ M / Fourier.momentumBracket c ^ M) := by
  have hcx := momentumBracket_center_le hR hx
  have hpc : 0 < Fourier.momentumBracket c ^ M := pow_pos (lt_of_lt_of_le zero_lt_one (one_le_momentumBracket c)) M
  have hpx : 0 < Fourier.momentumBracket x ^ M := pow_pos (lt_of_lt_of_le zero_lt_one (one_le_momentumBracket x)) M
  have hp : Fourier.momentumBracket c ^ M ≤ (2 + R) ^ M * Fourier.momentumBracket x ^ M := by
    simpa only [mul_pow] using pow_le_pow_left₀ (zero_le_one.trans (one_le_momentumBracket c)) hcx M
  apply (norm_iteratedFDeriv_le_of_spatialNorm hB h hj x).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (div_le_div_iff₀ hpx hpc).mpr
  calc
    _ ≤ B * ((2 + R) ^ M * Fourier.momentumBracket x ^ M) := mul_le_mul_of_nonneg_left hp hB
    _ = _ := by ring

end WaveTurbulence.Incoh
