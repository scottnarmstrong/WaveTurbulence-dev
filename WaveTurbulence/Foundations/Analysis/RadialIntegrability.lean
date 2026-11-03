/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import WaveTurbulence.Foundations.Analysis.RieszKernel

/-!
# Local integrability of radial powers

The local kernel integrability needed for the Morrey estimate. The proof
uses the polar integration theorem in Mathlib.
-/

public section

open scoped Real ENNReal
open MeasureTheory Metric Set

namespace WaveTurbulence.Analysis

variable {d : ℕ}

/-- A radial real power is locally integrable at the origin in dimension `d`
exactly above exponent `-d`. -/
theorem integrableOn_norm_rpow_ball_iff
    [NeZero d] {R s : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : Mom d => ‖x‖ ^ s) (ball 0 R) ↔ -(d : ℝ) < s := by
  let f : ℝ → ℝ := fun r => (Ioo (0 : ℝ) R).indicator (fun _ => r ^ s) r
  have hpolar := integrable_fun_norm_addHaar (μ := (volume : Measure (Mom d))) (f := f)
  have hleft : Integrable (fun x : Mom d => f ‖x‖) ↔
      IntegrableOn (fun x : Mom d => ‖x‖ ^ s) (ball 0 R) := by
    rw [← integrable_indicator_iff (isOpen_ball.measurableSet)]
    apply integrable_congr
    filter_upwards [(countable_singleton (0 : Mom d)).ae_notMem volume] with x hx
    have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx
    by_cases hxb : x ∈ ball (0 : Mom d) R
    · have hnorm : ‖x‖ ∈ Ioo (0 : ℝ) R := by
        simpa only [mem_Ioo, norm_pos_iff, mem_ball_zero_iff] using And.intro hx0 hxb
      simp only [f, Set.indicator_of_mem hnorm, Set.indicator_of_mem hxb]
    · have hnorm : ‖x‖ ∉ Ioo (0 : ℝ) R := by
        intro hn
        apply hxb
        simpa only [mem_ball_zero_iff] using hn.2
      simp only [f, Set.indicator_of_notMem hnorm, Set.indicator_of_notMem hxb]
  rw [hleft] at hpolar
  rw [hpolar]
  have hdim : Module.finrank ℝ (Mom d) = d := by
    calc
      Module.finrank ℝ (Mom d) = Module.finrank ℝ (Fin d → ℝ) :=
        (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).finrank_eq
      _ = d := by simp
  rw [hdim]
  have hcongr : IntegrableOn
      (fun y : ℝ => y ^ (d - 1) • f y) (Ioi 0) ↔
      IntegrableOn (fun y : ℝ => y ^ (s + (d : ℝ) - 1)) (Ioo 0 R) := by
    rw [← integrable_indicator_iff measurableSet_Ioi,
      ← integrable_indicator_iff measurableSet_Ioo]
    apply integrable_congr
    filter_upwards with y
    simp only [f, indicator_apply, smul_eq_mul]
    by_cases hyr : y ∈ Ioo (0 : ℝ) R
    · have hy0 : y ∈ Ioi (0 : ℝ) := hyr.1
      rw [ite_eq_left hy0, ite_eq_left hyr, ite_eq_left hyr]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hyr.1]
      congr 1
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))]
      push_cast
      ring
    · by_cases hy0 : y ∈ Ioi (0 : ℝ)
      · rw [ite_eq_left hy0, ite_eq_right hyr, ite_eq_right hyr, mul_zero]
      · rw [ite_eq_right hy0, ite_eq_right hyr]
  rw [hcongr, intervalIntegral.integrableOn_Ioo_rpow_iff hR]
  have hdreal : (1 : ℝ) ≤ d := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  constructor <;> intro h <;> linarith

/-- Translation of the radial kernel integral to the origin. -/
theorem lintegral_norm_sub_rpow_ball (x : Mom d) (R s : ℝ) :
    (∫⁻ y in ball x R, ENNReal.ofReal (‖x - y‖ ^ s)) =
      ∫⁻ z in ball (0 : Mom d) R, ENNReal.ofReal (‖z‖ ^ s) := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  have hh := lintegral_sub_left_eq_self (μ := (volume : Measure (Mom d)))
    ((ball (0 : Mom d) R).indicator fun z => ENNReal.ofReal (‖z‖ ^ s)) x
  rw [← hh]
  apply lintegral_congr
  intro y
  have hm : y ∈ ball x R ↔ x - y ∈ ball (0 : Mom d) R := by
    simp only [mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hy : y ∈ ball x R
  · rw [indicator_of_mem hy, indicator_of_mem (hm.mp hy)]
  · rw [indicator_of_notMem hy, indicator_of_notMem (mt hm.mpr hy)]

/-- The integral of a radial power on a ball has its expected homogeneity.
The formula also holds for nonintegrable powers in extended real form. -/
theorem lintegral_norm_rpow_ball_scale {R : ℝ} (hR : 0 < R) (s : ℝ) :
    (∫⁻ z in ball (0 : Mom d) R, ENNReal.ofReal (‖z‖ ^ s)) =
      ENNReal.ofReal (R ^ ((d : ℝ) + s)) *
        ∫⁻ z in ball (0 : Mom d) 1, ENNReal.ofReal (‖z‖ ^ s) := by
  let H : Mom d → ℝ≥0∞ :=
    (ball (0 : Mom d) R).indicator fun z => ENNReal.ofReal (‖z‖ ^ s)
  have hm : Measurable H := (by fun_prop : Measurable
    (fun z : Mom d => ENNReal.ofReal (‖z‖ ^ s))).indicator measurableSet_ball
  have hp (z : Mom d) : H (R • z) = ENNReal.ofReal (R ^ s) *
      (ball (0 : Mom d) 1).indicator (fun z => ENNReal.ofReal (‖z‖ ^ s)) z := by
    have heq : R • z ∈ ball (0 : Mom d) R ↔ z ∈ ball (0 : Mom d) 1 := by
      simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      exact mul_lt_iff_lt_one_right hR
    dsimp only [H]
    by_cases hz : z ∈ ball (0 : Mom d) 1
    · rw [indicator_of_mem (heq.mpr hz), indicator_of_mem hz, norm_smul,
        Real.norm_eq_abs, abs_of_pos hR, Real.mul_rpow hR.le (norm_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    · rw [indicator_of_notMem (mt heq.mp hz), indicator_of_notMem hz, mul_zero]
  have hs := lintegral_comp_dilation hm (0 : Mom d) hR
  simp only [sub_zero, zero_add] at hs
  simp_rw [hp] at hs
  rw [lintegral_const_mul _ ((by fun_prop : Measurable
    (fun z : Mom d => ENNReal.ofReal (‖z‖ ^ s))).indicator measurableSet_ball),
    lintegral_indicator measurableSet_ball,
    lintegral_indicator measurableSet_ball] at hs
  have hmul := congrArg (fun v => ENNReal.ofReal (R ^ d) * v) hs
  simp only [← mul_assoc] at hmul
  have hc : ENNReal.ofReal (R ^ d) * ENNReal.ofReal ((R ^ d)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hR.le d),
      mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), ENNReal.ofReal_one]
  rw [hc, one_mul] at hmul
  rw [← hmul, ← ENNReal.ofReal_mul (pow_nonneg hR.le d),
    ← Real.rpow_natCast, ← Real.rpow_add hR]


end WaveTurbulence.Analysis
