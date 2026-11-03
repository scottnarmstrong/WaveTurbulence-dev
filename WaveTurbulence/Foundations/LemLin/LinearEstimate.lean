/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.LinearWindow
public import WaveTurbulence.Foundations.LemLin.WindowParameters

/-!
# TARGET Lemma `lemlin`

The source estimate is uniform in the spatial translation, modulation, and
initial time. We prove it for all real momenta in the source norm range, a
stronger statement than restricting to lattice momenta. Explicit smallness
conditions `δ ≤ 1` and `γ + η ≤ 1` suffice. The last theorem records the
additional lower-momentum-bound consequence needed in FINDINGS F23.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set

/-- The uniform constant for both branches of the source minimum. -/
@[expose] noncomputable def linearEstimateConstant (d : ℕ) : ℝ :=
  max ((3 : ℝ) ^ d) (linearCancellationConstant d)

theorem linearEstimateConstant_nonneg (d : ℕ) : 0 ≤ linearEstimateConstant d :=
  (by positivity : (0 : ℝ) ≤ 3 ^ d).trans (le_max_left _ _)

/-- TARGET `lemlin`, L1536–L1543, with an explicit dimension-dependent constant. -/
theorem lemlin {d : ℕ} {L δ γ η : ℝ} (hL : 1 ≤ L)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hγη : γ + η ≤ 1)
    (a r ξ : Mom d) (hrlo : L⁻¹ ≤ ‖r‖) (hrhi : ‖r‖ ≤ L ^ (-γ + η)) (τ : ℝ) :
    (∫ s in Icc τ (τ + δ * L ^ (2 * γ)), ‖linearLatticeSum L a (s • r + ξ)‖) ≤
      linearEstimateConstant d * min (δ * L ^ ((d : ℝ) + 2 * γ)) (L ^ d / ‖r‖) := by
  have hLpos : 0 < L := by linarith
  have hrpos : 0 < ‖r‖ := (inv_pos.mpr hLpos).trans_le hrlo
  have hr : r ≠ 0 := norm_pos_iff.mp hrpos
  have hT : 0 ≤ δ * L ^ (2 * γ) := mul_nonneg hδ0 (Real.rpow_nonneg hLpos.le _)
  have ht := integral_linear_flow_trivial hL hT a r ξ τ
  have hc := integral_linear_flow_cancellation hL hT a r ξ hr
    (source_window_short hL hδ0 hδ1 hγη r hrhi) τ
  have heq : (3 : ℝ) ^ d * L ^ d * (δ * L ^ (2 * γ)) =
      (3 : ℝ) ^ d * (δ * L ^ ((d : ℝ) + 2 * γ)) := by
    rw [Real.rpow_add hLpos, Real.rpow_natCast]
    ring
  rw [heq] at ht
  rw [mul_min_of_nonneg _ _ (linearEstimateConstant_nonneg d)]
  apply le_min
  · exact ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg hδ0 (Real.rpow_nonneg hLpos.le _)))
  · rw [mul_div_assoc] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (div_nonneg (pow_nonneg hLpos.le _) hrpos.le))

/-- The additional bound needed for TARGET `sumint` case (d), FINDINGS F23.
The source lower bound on the momentum replaces `‖r‖⁻¹` by `L`. -/
theorem lemlin_lower_momentum_bound {d : ℕ} {L δ γ η : ℝ} (hL : 1 ≤ L)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hγη : γ + η ≤ 1)
    (a r ξ : Mom d) (hrlo : L⁻¹ ≤ ‖r‖) (hrhi : ‖r‖ ≤ L ^ (-γ + η)) (τ : ℝ) :
    (∫ s in Icc τ (τ + δ * L ^ (2 * γ)), ‖linearLatticeSum L a (s • r + ξ)‖) ≤
      linearEstimateConstant d * L ^ (d + 1) := by
  have hLpos : 0 < L := by linarith
  have hrpos : 0 < ‖r‖ := (inv_pos.mpr hLpos).trans_le hrlo
  have hb : L ^ d / ‖r‖ ≤ L ^ (d + 1) := by
    apply (div_le_iff₀ hrpos).mpr
    have hi : 1 ≤ L * ‖r‖ := (inv_le_iff_one_le_mul₀' hLpos).mp hrlo
    have hm := mul_le_mul_of_nonneg_left hi (pow_nonneg hLpos.le d)
    simpa only [mul_one, pow_succ, mul_assoc] using hm
  exact (lemlin hL hδ0 hδ1 hγη a r ξ hrlo hrhi τ).trans
    (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hb) (linearEstimateConstant_nonneg d))

end WaveTurbulence.LemLin
