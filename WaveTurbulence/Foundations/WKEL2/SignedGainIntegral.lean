/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.GainAbs
public import WaveTurbulence.Foundations.WKEL2.ResonantIntegral
public import WaveTurbulence.Foundations.WKE.CollisionOp

/-!
# The signed gain integral and its intrinsic delta reading

The signed Bochner integral is compared with its absolute extended majorant.
The equality with `collisionTerm 0` is used only where actual absolute
integrability has been proved.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Signed gain integrated against resonant measure with the exact delta normalization. -/
@[expose] def resonantGain (e : Mom d) (f₁ f₂ f₃ : Mom d → ℝ) (k : Mom d) : ℝ :=
  (1 / 2 : ℝ) * ∫ p, f₁ (k + p.1) * f₂ (k + p.1 + p.2) * f₃ (k + p.2) ∂resonantMeasure e

/-- The signed gain integral is Borel measurable in the output momentum. -/
theorem measurable_resonantGain (e : Mom d) (hd : 2 ≤ d) {f₁ f₂ f₃ : Mom d → ℝ}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) :
    Measurable (resonantGain e f₁ f₂ f₃) := by
  let := resonantMeasure_finiteOnCompacts e hd
  have hJ : Measurable (fun q : Mom d × (Mom d × Mom d) =>
      f₁ (q.1 + q.2.1) * f₂ (q.1 + q.2.1 + q.2.2) * f₃ (q.1 + q.2.2)) :=
    ((h₁.comp (by fun_prop)).mul (h₂.comp (by fun_prop))).mul (h₃.comp (by fun_prop))
  exact measurable_const.mul hJ.stronglyMeasurable.integral_prod_right.measurable

/-- Absolute signed gain is controlled by the nonnegative extended gain, including at exceptional outputs. -/
theorem ofReal_abs_resonantGain_le (e : Mom d) (f₁ f₂ f₃ : Mom d → ℝ) (k : Mom d) :
    ENNReal.ofReal |resonantGain e f₁ f₂ f₃ k| ≤
      ENNReal.ofReal (1 / 2 : ℝ) * absoluteGain e f₁ f₂ f₃ k := by
  have h := enorm_integral_le_lintegral_enorm (μ := resonantMeasure e)
    (fun p : Mom d × Mom d => f₁ (k + p.1) * f₂ (k + p.1 + p.2) * f₃ (k + p.2))
  have h' : ENNReal.ofReal |∫ p, f₁ (k + p.1) * f₂ (k + p.1 + p.2) * f₃ (k + p.2)
      ∂resonantMeasure e| ≤ absoluteGain e f₁ f₂ f₃ k := by
    simpa only [absoluteGain, ← ofReal_norm, Real.norm_eq_abs, abs_mul,
      ENNReal.ofReal_mul' (abs_nonneg _)] using h
  rw [resonantGain, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact mul_le_mul' le_rfl h'

/-- Finiteness of the absolute gain gives actual signed kernel integrability. -/
theorem integrable_gainKernel_of_absoluteGain_lt_top (e : Mom d)
    {f₁ f₂ f₃ : Mom d → ℝ} (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃)
    (k : Mom d) (hfinite : absoluteGain e f₁ f₂ f₃ k < ⊤) :
    Integrable (fun p : Mom d × Mom d =>
      f₁ (k + p.1) * f₂ (k + p.1 + p.2) * f₃ (k + p.2)) (resonantMeasure e) := by
  have hm : Measurable (fun p : Mom d × Mom d =>
      f₁ (k + p.1) * f₂ (k + p.1 + p.2) * f₃ (k + p.2)) :=
    ((h₁.comp (by fun_prop)).mul (h₂.comp (by fun_prop))).mul (h₃.comp (by fun_prop))
  refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
  simpa only [absoluteGain, norm_mul, Real.norm_eq_abs, ENNReal.ofReal_mul' (abs_nonneg _)] using hfinite

/-- The signed resonant integral agrees with the actual gain term wherever the kernel is integrable. -/
theorem resonantGain_eq_collisionTerm_zero {e : Mom d} (he : ‖e‖ = 1)
    (f₁ f₂ f₃ : Mom d → ℝ) (k : Mom d)
    (hi : Integrable (fun p : Mom d × Mom d =>
      f₁ (k + p.1) * f₂ (k + p.1 + p.2) * f₃ (k + p.2)) (resonantMeasure e)) :
    resonantGain e f₁ f₂ f₃ k = collisionTerm 0 f₁ f₂ f₃ k := by
  unfold resonantGain
  rw [integral_resonantMeasure_eq_two_deltaInt he hi]
  change (1 / 2 : ℝ) * (2 * deltaInt (fun a b => f₁ (k + a) * f₂ (k + a + b) * f₃ (k + b))) = _
  change _ = deltaInt (fun a b => f₁ (k + a) * f₂ (k + a + b) * f₃ (k + b))
  ring

end WaveTurbulence.WKEL2
