/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Positive affine rescaling of arbitrary closed time windows

The enlarged local domains have interval length up to three. The exact
closed-interval identity retains these endpoints without rounding or
changing strict source inequalities.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Positive affine rescaling of an ordered closed interval. -/
theorem integral_Icc_affine (f : ℝ → ℝ) {c a b : ℝ} (hc : 0 < c) (hab : a ≤ b)
    (t : ℝ) :
    (∫ s in Icc a b, f (c*(s-t))) =
      c⁻¹ * ∫ u in Icc (c*(a-t)) (c*(b-t)), f u := by
  have he (s : ℝ) : c*s+ -(c*t) = c*(s-t) := by ring
  have hf : (fun s => f (c*(s-t))) = fun s => f (c*s+ -(c*t)) := by
    funext s
    rw [he]
  rw [hf, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_mul_add f hc.ne' (-(c*t)), he a, he b,
    intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left (sub_le_sub_right hab t) hc.le),
    integral_Icc_eq_integral_Ioc, smul_eq_mul]

/-- An affine time window contained in a symmetric window costs at most
its positive rescaling factor times the symmetric integral. -/
theorem integral_Icc_affine_le_symmetric (f : ℝ → ℝ) {c a b B : ℝ}
    (hc : 0 < c) (hab : a ≤ b) (t : ℝ)
    (hi : IntegrableOn f (Icc (-B) B)) (hn : ∀ u, 0 ≤ f u)
    (hlo : -B ≤ c*(a-t)) (hhi : c*(b-t) ≤ B) :
    (∫ s in Icc a b, f (c*(s-t))) ≤ c⁻¹ * ∫ u in Icc (-B) B, f u := by
  rw [integral_Icc_affine f hc hab]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
  apply setIntegral_mono_set hi (ae_of_all _ hn)
  exact ae_of_all _ (fun _ hu => ⟨hlo.trans hu.1, hu.2.trans hhi⟩)

end WaveTurbulence.SumintPar
