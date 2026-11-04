/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothRectangle
public import WaveTurbulence.Foundations.Fourier.TwoCoordinateIntegration

/-!
# Uniform mixed derivative mass of rectangular windows

The constant four is independent of both interval endpoints and smoothing
width. This supplies the right-hand side of the landed phase lemma.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Tensorization of the two one-dimensional variation bounds. -/
theorem lintegral_mixedTimePartial_smoothRectangle_le {ε : ℝ} (hε : 0 < ε)
    (a b : Fin 2 → ℝ) (hab : a ≤ b) :
    (∫⁻ t, ‖Fourier.mixedTimePartial (smoothRectangle ε a b) t‖ₑ) ≤ 4 := by
  let f (j : Fin 2) := deriv (smoothInterval ε (a j) (b j))
  have hi (j : Fin 2) : Integrable (f j) :=
    ((contDiff_smoothInterval ε (a j) (b j)).continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
      (hasCompactSupport_smoothInterval hε (hab j)).deriv
  have hm (j : Fin 2) : Measurable (fun t => ‖f j t‖ₑ) :=
    ((contDiff_smoothInterval ε (a j) (b j)).continuous_deriv (by norm_num)).measurable.enorm
  have hbnd (j : Fin 2) : (∫⁻ t, ‖f j t‖ₑ) ≤ 2 := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi j)]
    exact (ENNReal.ofReal_le_ofReal (integral_norm_deriv_smoothInterval_le hε (a j) (b j) (hab j))).trans_eq (by norm_num)
  have he (t : Fin 2 → ℝ) : ‖Fourier.mixedTimePartial (smoothRectangle ε a b) t‖ₑ =
      ‖f 0 (t 0)‖ₑ * ‖f 1 (t 1)‖ₑ := by
    rw [mixedTimePartial_smoothRectangle]
    simp only [f, ← ofReal_norm, norm_mul, Complex.norm_real]
    exact ENNReal.ofReal_mul (norm_nonneg _)
  simp_rw [he]
  have hmm : Measurable (fun t : Fin 2 → ℝ => ‖f 0 (t 0)‖ₑ * ‖f 1 (t 1)‖ₑ) :=
    ((hm 0).comp (measurable_pi_apply 0)).mul ((hm 1).comp (measurable_pi_apply 1))
  rw [Fourier.lintegral_two_coordinates hmm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have heq : (∫⁻ u : ℝ, ∫⁻ v : ℝ, ‖f 0 u‖ₑ * ‖f 1 v‖ₑ) =
      (∫⁻ u : ℝ, ‖f 0 u‖ₑ) * ∫⁻ v : ℝ, ‖f 1 v‖ₑ := by
    simp_rw [lintegral_const_mul _ (hm 1)]
    exact lintegral_mul_const _ (hm 0)
  rw [heq]
  exact (mul_le_mul' (hbnd 0) (hbnd 1)).trans_eq (by norm_num)

end WaveTurbulence.Incoh
