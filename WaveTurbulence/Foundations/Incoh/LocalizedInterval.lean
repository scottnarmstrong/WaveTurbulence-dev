/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothStepMass
public import WaveTurbulence.Foundations.Fourier.CutoffControl

/-!
# Localized interval windows with uniform first variation

The fixed smooth cutoff supplies compact support. Both the mass and the
first-derivative mass are uniform in the interval endpoints and smoothing width.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- A literal interval approximation localized by the fixed time cutoff. -/
@[expose] def localizedInterval (χ : ℝ → ℝ) (ε a b t : ℝ) : ℝ :=
  χ t * smoothInterval ε a b t

@[fun_prop] theorem contDiff_localizedInterval {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (ε a b : ℝ) : ContDiff ℝ ∞ (localizedInterval χ ε a b) :=
  hχ.mul (contDiff_smoothInterval ε a b)

theorem hasCompactSupport_localizedInterval {χ : ℝ → ℝ} (hcχ : HasCompactSupport χ)
    (ε a b : ℝ) : HasCompactSupport (localizedInterval χ ε a b) := hcχ.mul_right

theorem integral_norm_localizedInterval_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {ε a b : ℝ} (hε : 0 < ε) (hab : a ≤ b) :
    (∫ t, ‖localizedInterval χ ε a b t‖) ≤ ∫ t, ‖χ t‖ := by
  apply integral_mono
    (((contDiff_localizedInterval hχ ε a b).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_localizedInterval hcχ ε a b)).norm)
    ((hχ.continuous.integrable_of_hasCompactSupport hcχ).norm)
  intro t
  dsimp only
  rw [localizedInterval, norm_mul, Real.norm_of_nonneg (smoothInterval_nonneg hε hab t)]
  exact mul_le_of_le_one_right (norm_nonneg _) (smoothInterval_le_one _ _ _ _)

/-- The localized window never exceeds the modulus of the fixed cutoff. -/
theorem norm_localizedInterval_le {χ : ℝ → ℝ} {ε a b : ℝ} (hε : 0 < ε) (hab : a ≤ b) (t : ℝ) :
    ‖localizedInterval χ ε a b t‖ ≤ ‖χ t‖ := by
  rw [localizedInterval, norm_mul, Real.norm_of_nonneg (smoothInterval_nonneg hε hab t)]
  exact mul_le_of_le_one_right (norm_nonneg _) (smoothInterval_le_one _ _ _ _)

/-- Only the first variation of the interval boundary enters the moment estimate. -/
theorem integral_norm_deriv_localizedInterval_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (h : Fourier.CutoffControl χ)
    {ε a b : ℝ} (hε : 0 < ε) (hab : a ≤ b) :
    (∫ t, ‖deriv (localizedInterval χ ε a b) t‖) ≤ (∫ t, ‖deriv χ t‖) + 2 * h.bound := by
  have hiχ : Integrable (deriv χ) :=
    (hχ.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport hcχ.deriv
  have hiw : Integrable (deriv (smoothInterval ε a b)) :=
    ((contDiff_smoothInterval ε a b).continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
      (hasCompactSupport_smoothInterval hε hab).deriv
  have hi : Integrable (deriv (localizedInterval χ ε a b)) :=
    ((contDiff_localizedInterval hχ ε a b).continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
      (hasCompactSupport_localizedInterval hcχ ε a b).deriv
  have hC : 0 ≤ h.bound := zero_le_one.trans h.one_le_bound
  calc
    _ ≤ ∫ t, ‖deriv χ t‖ + h.bound * ‖deriv (smoothInterval ε a b) t‖ := by
      apply integral_mono hi.norm (hiχ.norm.add (hiw.norm.const_mul _))
      intro t
      dsimp only [Pi.add_apply]
      rw [show deriv (localizedInterval χ ε a b) t = deriv χ t * smoothInterval ε a b t +
        χ t * deriv (smoothInterval ε a b) t from
          deriv_mul ((hχ.differentiable (by simp)) t)
            (((contDiff_smoothInterval ε a b).differentiable (by simp)) t)]
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_mul]
      apply add_le_add
      · exact mul_le_of_le_one_right (norm_nonneg _)
          (by rw [Real.norm_of_nonneg (smoothInterval_nonneg hε hab t)]; exact smoothInterval_le_one _ _ _ _)
      · exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using h.abs_le t) (norm_nonneg _)
    _ = (∫ t, ‖deriv χ t‖) + h.bound * ∫ t, ‖deriv (smoothInterval ε a b) t‖ := by
      rw [integral_add hiχ.norm (hiw.norm.const_mul _), integral_const_mul]
    _ ≤ _ := add_le_add le_rfl ((mul_le_mul_of_nonneg_left
      (integral_norm_deriv_smoothInterval_le hε a b hab) hC).trans_eq (mul_comm _ _))

end WaveTurbulence.Incoh
