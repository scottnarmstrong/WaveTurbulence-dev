/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.RadialWeight
public import WaveTurbulence.Foundations.WKEL2.WeightedKernelLp
public import WaveTurbulence.Foundations.WKEL2.PolarDensity

/-!
# Nonnegative radial measure formula for A_k
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Radial integration of the Japanese decay kernel gives exactly `A_k`. -/
theorem lintegral_radialWeight_measure (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (k θ : Mom d) (hθ : ‖θ‖ = 1) :
    (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (japaneseDecay (2 * s) (k + r.1 • θ))
      ∂Measure.volumeIoiPow (d - 3)) = ENNReal.ofReal (radialWeight d s k θ) := by
  have hm : Measurable (fun r : ℝ => ENNReal.ofReal (japaneseDecay (2 * s) (k + r • θ))) := by
    have hb : Continuous (fun r : ℝ => 1 + ‖k + r • θ‖ ^ 2) := by fun_prop
    exact (hb.rpow_const (fun _ => Or.inl (by positivity))).measurable.ennreal_ofReal
  rw [lintegral_volumeIoiPow_comp (d - 3) hm]
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun r => (1 + ‖k + r • θ‖ ^ 2) ^ (-s) * r ^ (d - 3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg hr.le _)
  rw [radialWeight, ofReal_integral_eq_lintegral_ofReal
    (integrable_radialWeight hd s hs k θ hθ) hn]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [japaneseDecay, show -(2 * s) / 2 = -s by ring,
    ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  exact mul_comm _ _

/-- Measurability of A_k on the ambient unit sphere. -/
theorem measurable_radialWeight_unitSphere (s : ℝ) (k : Mom d) :
    Measurable (fun θ : sphere (0 : Mom d) 1 => radialWeight d s k θ.1) := by
  have hb : Continuous (fun q : sphere (0 : Mom d) 1 × ℝ =>
      1 + ‖k + q.2 • q.1.1‖ ^ 2) := by fun_prop
  have hc : Continuous (fun q : sphere (0 : Mom d) 1 × ℝ =>
      (1 + ‖k + q.2 • q.1.1‖ ^ 2) ^ (-s) * q.2 ^ (d - 3)) :=
    (hb.rpow_const (fun _ => Or.inl (by positivity))).mul (continuous_snd.pow _)
  exact hc.stronglyMeasurable.integral_prod_right.measurable

end WaveTurbulence.WKEL2
