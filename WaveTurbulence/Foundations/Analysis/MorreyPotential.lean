/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.SmoothRiesz
public import WaveTurbulence.Foundations.Analysis.RadialIntegrability
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Hölder bound for the Morrey potential

This is the analytic estimate before evaluating the geometric kernel
constant on a square. In dimension two the conjugate exponent must be
strictly less than two.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Morrey's potential estimate, with all geometric constants and norms
explicit, for smooth functions on a convex set. -/
theorem enorm_mul_volume_le_morreyPotential {f : Mom d → F} (hf : ContDiff ℝ 1 f)
    (hd : 0 < d) {S : Set (Mom d)} (hS : MeasurableSet S) (hconv : Convex ℝ S)
    {x : Mom d} (hx : x ∈ S) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ y ∈ S, ‖x - y‖ ≤ D) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ‖f x‖ₑ * volume S ≤
      (∫⁻ y in S, ‖f y‖ₑ ^ p) ^ (1 / p) * (volume S) ^ (1 / q) +
      ENNReal.ofReal (D ^ d / d) *
        ((∫⁻ z in S, ENNReal.ofReal (‖x - z‖ ^ ((1 : ℝ) - d)) ^ q) ^ (1 / q) *
          (∫⁻ z in S, ‖fderiv ℝ f z‖ₑ ^ p) ^ (1 / p)) := by
  have hfirst := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) hpq
    hf.continuous.enorm.measurable.aemeasurable
    (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    one_mul, Measure.restrict_apply_univ] at hfirst
  have hkm : Measurable (fun z : Mom d => ENNReal.ofReal (‖x - z‖ ^ ((1 : ℝ) - d))) :=
    by fun_prop
  have hsecond := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) hpq.symm
    hkm.aemeasurable (hf.continuous_fderiv (by norm_num)).enorm.measurable.aemeasurable
  exact (enorm_mul_volume_le_riesz hf hd hS hconv hx hD hdiam).trans
    (add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (by positivity)))

/-- The unit-ball integral of the conjugate power of the Riesz kernel.
This depends only on dimension and the exponent. -/
@[expose] noncomputable def rieszPowerIntegral (d : ℕ) (q : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Metric.ball (0 : Mom d) 1,
    ENNReal.ofReal (‖z‖ ^ (((1 : ℝ) - d) * q))

/-- Finiteness of the Morrey kernel constant, precisely in the required
locally integrable range. For `d = 2`, this requires `q < 2`. -/
theorem rieszPowerIntegral_lt_top (hd : 0 < d) {q : ℝ}
    (hq : -(d : ℝ) < ((1 : ℝ) - d) * q) : rieszPowerIntegral d q < ⊤ := by
  let : NeZero d := ⟨hd.ne'⟩
  exact ((integrableOn_norm_rpow_ball_iff (d := d) (R := 1) (by norm_num)).2 hq).lintegral_lt_top

/-- Bound for the kernel on any set inside a ball, including its exact
scale dependence. No regularity of the set beyond inclusion is needed. -/
theorem lintegral_riesz_power_le {S : Set (Mom d)} {x : Mom d} {R q : ℝ}
    (hR : 0 < R) (hq : 0 ≤ q) (hsub : S ⊆ Metric.ball x R) :
    (∫⁻ z in S, ENNReal.ofReal (‖x - z‖ ^ ((1 : ℝ) - d)) ^ q) ≤
      ENNReal.ofReal (R ^ ((d : ℝ) + ((1 : ℝ) - d) * q)) * rieszPowerIntegral d q := by
  calc
    (∫⁻ z in S, ENNReal.ofReal (‖x - z‖ ^ ((1 : ℝ) - d)) ^ q) =
        ∫⁻ z in S, ENNReal.ofReal (‖x - z‖ ^ (((1 : ℝ) - d) * q)) := by
      apply lintegral_congr
      intro z
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hq,
        ← Real.rpow_mul (norm_nonneg _)]
    _ ≤ ∫⁻ z in Metric.ball x R,
        ENNReal.ofReal (‖x - z‖ ^ (((1 : ℝ) - d) * q)) :=
      lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ = _ := by
      rw [lintegral_norm_sub_rpow_ball, lintegral_norm_rpow_ball_scale hR]
      rfl

/-- The Morrey potential estimate with a uniform geometric kernel bound.
The constant is finite whenever `-(d:ℝ) < (1-d)q`. -/
theorem enorm_mul_volume_le_morrey_ball {f : Mom d → F} (hf : ContDiff ℝ 1 f)
    (hd : 0 < d) {S : Set (Mom d)} (hS : MeasurableSet S) (hconv : Convex ℝ S)
    {x : Mom d} (hx : x ∈ S) {R : ℝ} (hR : 0 < R)
    (hsub : S ⊆ Metric.ball x R) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ‖f x‖ₑ * volume S ≤
      (∫⁻ y in S, ‖f y‖ₑ ^ p) ^ (1 / p) * (volume S) ^ (1 / q) +
      ENNReal.ofReal (R ^ d / d) *
        ((ENNReal.ofReal (R ^ ((d : ℝ) + ((1 : ℝ) - d) * q)) *
          rieszPowerIntegral d q) ^ (1 / q) *
            (∫⁻ z in S, ‖fderiv ℝ f z‖ₑ ^ p) ^ (1 / p)) := by
  have hh := enorm_mul_volume_le_morreyPotential hf hd hS hconv hx hR
    (fun y hy => (show ‖x - y‖ < R by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hsub hy).le) hpq
  refine hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity)))
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact ENNReal.rpow_le_rpow (lintegral_riesz_power_le hR hpq.symm.nonneg hsub)
    (one_div_nonneg.mpr hpq.symm.nonneg)

end WaveTurbulence.Analysis
