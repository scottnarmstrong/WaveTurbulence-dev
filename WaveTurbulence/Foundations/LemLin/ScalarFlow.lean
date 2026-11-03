/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarPeriod

/-!
# Scalar cancellation on a short time interval

The change of variables in TARGET `lemlin`. A time interval whose frequency
image fits inside one lattice period costs the reciprocal frequency speed.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set

/-- Positive frequency speed: a short time interval lies in one frequency cell. -/
theorem integral_scalar_flow_pos {L T r : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    (hr : 0 < r) (hshort : r * T ≤ L) (a ξ τ : ℝ) :
    (∫ s in Icc τ (τ + T), ‖scalarLatticeSum L a (r * s + ξ)‖) ≤
      L * scalarFourierMass / r := by
  let f : ℝ → ℝ := fun u => ‖scalarLatticeSum L a u‖
  have hc : Continuous f := (continuous_scalarLatticeSum hL a).norm
  have hτ : τ ≤ τ + T := by linarith
  have hu : r * τ + ξ ≤ r * (τ + T) + ξ := by nlinarith
  have hv : r * (τ + T) + ξ ≤ r * τ + ξ + L := by nlinarith
  have hm := intervalIntegral.integral_mono_interval (f := f) (μ := volume) le_rfl hu hv
    (ae_of_all _ (fun u => norm_nonneg _)) (hc.intervalIntegrable (μ := volume) _ _)
  have hp := integral_scalarLatticeSum_period hL a (r * τ + ξ)
  rw [← intervalIntegral.integral_of_le (by linarith : r * τ + ξ ≤ r * τ + ξ + L)] at hp
  have he := intervalIntegral.smul_integral_comp_mul_add f r ξ (a := τ) (b := τ + T)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ]
  apply (le_div_iff₀ hr).mpr
  calc
    _ = ∫ u in r * τ + ξ..r * (τ + T) + ξ, f u := by
      simpa only [smul_eq_mul, mul_comm] using he
    _ ≤ _ := hm.trans hp

/-- Either frequency direction gives the same cancellation estimate. -/
theorem integral_scalar_flow {L T r : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    (hr : r ≠ 0) (hshort : |r| * T ≤ L) (a ξ τ : ℝ) :
    (∫ s in Icc τ (τ + T), ‖scalarLatticeSum L a (r * s + ξ)‖) ≤
      L * scalarFourierMass / |r| := by
  rcases lt_or_gt_of_ne hr with hr | hr
  · have h := integral_scalar_flow_pos hL hT (neg_pos.mpr hr)
      (by simpa only [abs_of_neg hr] using hshort) a (-ξ) τ
    have he : (fun s : ℝ => ‖scalarLatticeSum L a (-r * s + -ξ)‖) =
        fun s => ‖scalarLatticeSum L a (r * s + ξ)‖ := by
      funext s
      rw [show -r * s + -ξ = -(r * s + ξ) by ring,
        norm_scalarLatticeSum_neg hL]
    simpa only [he, abs_of_neg hr] using h
  · simpa only [abs_of_pos hr] using integral_scalar_flow_pos hL hT hr
      (by simpa only [abs_of_pos hr] using hshort) a ξ τ

end WaveTurbulence.LemLin
