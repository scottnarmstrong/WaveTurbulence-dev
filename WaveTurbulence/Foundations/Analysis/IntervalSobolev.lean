/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Sobolev bounds on intervals

The unit-interval estimate used in TARGET (sobolev), L2314–2316, is proved for
normed real vector spaces, hence in particular for complex scalars and Hilbert
spaces of square-summable sequences. Integrals use Lebesgue measure.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fundamental theorem of calculus bounds displacement by the total speed
on any containing interval. No completeness assumption on the range is needed. -/
theorem norm_sub_le_integral_norm_deriv {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖f t - f s‖ ≤ ∫ x in Icc a b, ‖deriv f x‖ := by
  have hc := hf.continuous_deriv_one.norm
  have hbound {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      ‖f v - f u‖ ≤ ∫ x in Icc a b, ‖deriv f x‖ := by
    have hftc := norm_sub_le_integral_of_norm_deriv_le_of_le huv
      hf.continuous.continuousOn
      (hf.differentiable (by norm_num)).differentiableOn
      (Filter.Eventually.of_forall fun _ _ => le_rfl)
      (hc.intervalIntegrable u v)
    have hm := intervalIntegral.integral_mono_interval hu.1 huv hv.2
      (Filter.Eventually.of_forall fun x => norm_nonneg (deriv f x))
      (hc.intervalIntegrable (μ := volume) a b)
    exact hftc.trans (hm.trans_eq (by
      rw [intervalIntegral.integral_of_le (hu.1.trans (huv.trans hv.2)),
        integral_Icc_eq_integral_Ioc]))
  rcases le_total s t with h | h
  · exact hbound hs ht h
  · rw [norm_sub_rev]
    exact hbound ht hs h

/-- Pointwise `W¹,¹` bound, with the exact interval-length dependence.
The unit-length case is the one-dimensional seed of DH21 (10.5), L2428. -/
theorem norm_le_interval_sobolev_L1 {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    ‖f t‖ ≤ (b - a)⁻¹ * (∫ x in Icc a b, ‖f x‖) +
      ∫ x in Icc a b, ‖deriv f x‖ := by
  obtain ⟨s, hs, hmean⟩ := exists_le_setAverage
    (μ := volume) (s := Icc a b)
    (by simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]; linarith)
    (by simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true])
    hf.continuous.norm.integrableOn_Icc
  have hsbound : ‖f s‖ ≤ (b - a)⁻¹ * (∫ x in Icc a b, ‖f x‖) := by
    simpa only [setAverage_eq, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), smul_eq_mul] using hmean
  calc
    ‖f t‖ ≤ ‖f s‖ + ‖f t - f s‖ := norm_le_insert' _ _
    _ ≤ _ := add_le_add hsbound (norm_sub_le_integral_norm_deriv hf hs ht)

omit [NormedSpace ℝ E] in
/-- On a unit interval, the `L¹` norm of a continuous function is bounded by
its `L²` norm. This proof uses the nonnegative variance. -/
theorem integral_norm_le_sqrt_integral_sq {f : ℝ → E} (hf : Continuous f) (a : ℝ) :
    (∫ x in Icc a (a + 1), ‖f x‖) ≤
      Real.sqrt (∫ x in Icc a (a + 1), ‖f x‖ ^ 2) := by
  let m := ∫ x in Icc a (a + 1), ‖f x‖
  have hpos : 0 ≤ ∫ x in Icc a (a + 1), (‖f x‖ - m) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have heq : (∫ x in Icc a (a + 1), (‖f x‖ - m) ^ 2) =
      (∫ x in Icc a (a + 1), ‖f x‖ ^ 2) - m ^ 2 := by
    have hi := hf.norm.integrableOn_Icc (μ := volume) (a := a) (b := a + 1)
    have hc2 : Continuous (fun x => ‖f x‖ ^ 2) := (continuous_pow 2).comp hf.norm
    have hi2' := (hc2.integrableOn_Icc (μ := volume) (a := a) (b := a + 1)).integrable
    have hit : Integrable (fun x => 2 * ‖f x‖ * m)
        (volume.restrict (Icc a (a + 1))) := (hi.const_mul 2).mul_const m
    have hid : Integrable (fun x => ‖f x‖ ^ 2 - 2 * ‖f x‖ * m)
        (volume.restrict (Icc a (a + 1))) := hi2'.sub hit
    simp_rw [sub_sq]
    rw [integral_add (f := fun x => ‖f x‖ ^ 2 - 2 * ‖f x‖ * m)
      (g := fun _ => m ^ 2) hid (integrable_const _),
      integral_sub (f := fun x => ‖f x‖ ^ 2) (g := fun x => 2 * ‖f x‖ * m)
        hi2' hit]
    simp only [integral_mul_const, integral_const_mul, integral_const,
      Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
      add_sub_cancel_left, ENNReal.toReal_ofReal zero_le_one, smul_eq_mul, one_mul]
    dsimp [m]
    ring
  rw [heq] at hpos
  exact (Real.le_sqrt (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg
    fun _ => sq_nonneg _)).2 (sub_nonneg.mp hpos)

/-- TARGET (sobolev), L2314–2316: the `H¹` bound on every unit interval,
with constant one, for arbitrary normed real vector spaces. -/
theorem norm_le_interval_sobolev_L2 {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    {a t : ℝ} (ht : t ∈ Icc a (a + 1)) :
    ‖f t‖ ≤ Real.sqrt (∫ x in Icc a (a + 1), ‖f x‖ ^ 2) +
      Real.sqrt (∫ x in Icc a (a + 1), ‖deriv f x‖ ^ 2) := by
  have h := norm_le_interval_sobolev_L1 hf (by linarith : a < a + 1) ht
  simp only [add_sub_cancel_left, inv_one, one_mul] at h
  exact h.trans (add_le_add (integral_norm_le_sqrt_integral_sq hf.continuous a)
    (integral_norm_le_sqrt_integral_sq hf.continuous_deriv_one a))

/-- The counting-measure version of TARGET (sobolev). The index set can in
particular be `Fin d → ℤ`, representing the scaled lattice. Both square sums
are inside the time integral; the constant is independent of the index set. -/
theorem norm_apply_le_interval_sobolev_L2 {ι : Type*}
    {f : ℝ → lp (fun _ : ι => E) 2} (hf : ContDiff ℝ 1 f)
    {a t : ℝ} (ht : t ∈ Icc a (a + 1)) (k : ι) :
    ‖f t k‖ ≤ Real.sqrt (∫ x in Icc a (a + 1), ∑' j, ‖f x j‖ ^ 2) +
      Real.sqrt (∫ x in Icc a (a + 1), ∑' j, ‖deriv f x j‖ ^ 2) := by
  have heq (v : lp (fun _ : ι => E) 2) : ‖v‖ ^ 2 = ∑' j, ‖v j‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v
  simpa only [heq] using (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (f t) k).trans (norm_le_interval_sobolev_L2 hf ht)

end WaveTurbulence.Analysis
