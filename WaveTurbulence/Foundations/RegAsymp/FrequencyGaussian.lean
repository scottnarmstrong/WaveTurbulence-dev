/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import WaveTurbulence.Foundations.ClassJR.MCSRep
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # A fixed positive integrable density for temporal-symbol normalization -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped ENNReal

/-- A fixed density on the literal two temporal Fourier variables. -/
@[expose] def frequencyGaussian (lam : ℝ × ℝ) : ℝ :=
  Real.exp (-lam.1^2)*Real.exp (-lam.2^2)

theorem frequencyGaussian_pos (lam : ℝ × ℝ) : 0 < frequencyGaussian lam := by
  unfold frequencyGaussian
  positivity

theorem measurable_frequencyGaussian : Measurable frequencyGaussian := by
  unfold frequencyGaussian
  fun_prop

theorem integrable_frequencyGaussian : Integrable frequencyGaussian := by
  have h : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : 0 < (1:ℝ))
  exact h.mul_prod h

/-- The fixed density has every temporal weight used by J3 in this packet. -/
theorem lintegral_wL_frequencyGaussian_lt_top {a : ℝ} (ha : a ≤ 1) :
    (∫⁻ lam : ℝ × ℝ, ClassJR.wL a lam * ENNReal.ofReal (frequencyGaussian lam)) < ⊤ := by
  have h : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : 0 < (1:ℝ))
  have hx : Integrable (fun x : ℝ => |x| * Real.exp (-x^2)) := by
    have hh := (integrable_mul_exp_neg_mul_sq (by norm_num : 0 < (1:ℝ))).norm
    simpa [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs] using hh
  have hi : Integrable (fun lam : ℝ × ℝ => (1+|lam.1| + |lam.2|)*frequencyGaussian lam) := by
    apply (((h.mul_prod h).add (hx.mul_prod h)).add (h.mul_prod hx)).congr
    exact ae_of_all _ (fun lam => by dsimp only [frequencyGaussian,Pi.add_apply]; ring)
  have hb (lam : ℝ × ℝ) : ClassJR.wL a lam ≤ ENNReal.ofReal (1+|lam.1| + |lam.2|) := by
    unfold ClassJR.wL
    have hbase : 1 ≤ (1+‖lam.1‖ₑ+‖lam.2‖ₑ) := by
      calc (1:ℝ≥0∞) ≤ 1+‖lam.1‖ₑ := le_self_add
           _ ≤ 1+‖lam.1‖ₑ+‖lam.2‖ₑ := le_self_add
    have hh := ENNReal.rpow_le_rpow_of_exponent_le hbase ha
    rw [ENNReal.rpow_one] at hh
    simpa only [ENNReal.ofReal_add (by positivity : 0 ≤ (1:ℝ)+|lam.1|) (abs_nonneg lam.2),
      ENNReal.ofReal_add (by norm_num : 0 ≤ (1:ℝ)) (abs_nonneg lam.1),ENNReal.ofReal_one,← ofReal_norm,Real.norm_eq_abs] using hh
  have hh := ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun lam => by have := (frequencyGaussian_pos lam).le; positivity))
  apply lt_of_le_of_lt (lintegral_mono (fun lam => ?_))
    (show (∫⁻ lam : ℝ × ℝ, ENNReal.ofReal ((1+|lam.1| + |lam.2|)*frequencyGaussian lam)) < ⊤ by
      rw [← hh]; exact ENNReal.ofReal_lt_top)
  rw [ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul' (hb lam) le_rfl

end WaveTurbulence.RegAsymp
