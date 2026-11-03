/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.DampedQuadratic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The sharp Fresnel integral with an explicit error

Gaussian regularization and uniform nonstationary tails give the Fresnel
coefficient for a sharp symmetric interval. The bare oscillatory
exponential is never treated as a Lebesgue-integrable function on ℝ.
-/

public section

open MeasureTheory Set Filter
open WaveTurbulence.NumberTheory
open scoped Topology

namespace WaveTurbulence.VdCB

/-- Removing Gaussian damping on a bounded interval. -/
theorem tendsto_integral_dampedQuadratic {E : ℕ → ℝ} (hE : Tendsto E atTop (𝓝 0))
    (hpos : ∀ n, 0 ≤ E n) (q a b : ℝ) :
    Tendsto (fun n => ∫ x in a..b, dampedQuadratic q (E n) x) atTop
      (𝓝 (∫ x in a..b, expPhase (q * x ^ 2 / 2))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Filter.Eventually.of_forall fun n =>
      (continuous_dampedQuadratic q (E n)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x _ => by
      rw [dampedQuadratic, norm_mul, norm_expPhase, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (hpos n)) (sq_nonneg x)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun x _ => by
      have hh := Real.continuous_exp.continuousAt.tendsto.comp
        ((hE.const_mul (-Real.pi)).mul_const (x ^ 2))
      have hhC := Complex.continuous_ofReal.continuousAt.tendsto.comp hh
      have hhF := hhC.congr (fun n => show
        (Complex.ofReal ∘ Real.exp ∘ (fun k : ℕ => -Real.pi * E k * x ^ 2)) n =
          (Real.exp (-Real.pi * E n * x ^ 2) : ℂ) by simp only [Function.comp_apply])
      have he : Tendsto (fun n => (Real.exp (-Real.pi * E n * x ^ 2) : ℂ)) atTop (𝓝 1) := by
        simpa only [mul_zero, zero_mul, Real.exp_zero, Complex.ofReal_one] using hhF
      simpa only [mul_one, dampedQuadratic] using tendsto_const_nhds.mul he

/-- Sharp positive-curvature Fresnel estimate, with the correct phase and
an error uniform in both the curvature and the cutoff. -/
theorem norm_integral_quadratic_sub_fresnel_le {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    ‖(∫ x in -r..r, expPhase (q * x ^ 2 / 2)) -
      expPhase (1 / 8) / (Real.sqrt q : ℂ)‖ ≤ 2 / (Real.pi * (q * r)) := by
  let E : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hE : Tendsto E atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos (n : ℕ) : 0 < E n := by dsimp only [E]; positivity
  let z : ℂ := (q : ℂ) * (-Complex.I)
  have hz : z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    dsimp only [z]
    simpa using neg_ne_zero.mpr hq.ne'
  have hzne : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hparam : Tendsto (fun n => ((E n : ℂ) - (q : ℂ) * Complex.I)) atTop (𝓝 z) := by
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp hE).sub_const ((q : ℂ) * Complex.I)
    simpa only [z, Complex.ofReal_zero, zero_sub, mul_neg, mul_one, Function.comp_apply] using hh
  have hp := (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hz).tendsto.comp hparam
  have hroot : z ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hzne)
  have hc := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).div hp hroot
  rw [fresnel_coefficient hq] at hc
  have hi := tendsto_integral_dampedQuadratic hE (fun n => (hpos n).le) q (-r) r
  have hl := hc.sub hi
  have hh : ‖expPhase (1 / 8) / (Real.sqrt q : ℂ) -
      ∫ x in -r..r, expPhase (q * x ^ 2 / 2)‖ ≤ 2 / (Real.pi * (q * r)) := by
    apply le_of_tendsto hl.norm
    apply Filter.Eventually.of_forall
    intro n
    simp only [Function.comp_apply, Pi.div_apply]
    rw [← integral_dampedQuadratic q (hpos n)]
    exact norm_integral_dampedQuadratic_sub_interval_le hq (hpos n) hr
  rwa [norm_sub_rev] at hh

end WaveTurbulence.VdCB
