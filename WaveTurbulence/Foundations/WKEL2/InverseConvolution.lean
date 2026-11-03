/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.InverseKernelLp
public import WaveTurbulence.Foundations.WKEL2.InverseExponent
public import WaveTurbulence.Foundations.WKEL2.WeightedKernelLp
public import WaveTurbulence.Foundations.WKEL2.HolderTranslation

/-!
# Uniform inverse-norm convolution bound

The spatial Hölder estimate behind research-note Lemma 4(a).
-/

public section

noncomputable section

open MeasureTheory Set Metric

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The spatial bound for M₂: the constant is independent of the translated center. -/
theorem exists_uniform_inverse_convolution (hd : 2 ≤ d) (a : ℝ)
    (ha : (d : ℝ) - 1 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Mom d,
      Integrable (fun x => japaneseDecay a (k + x) * ‖x‖⁻¹) ∧
      (∫ x, japaneseDecay a (k + x) * ‖x‖⁻¹) ≤ C := by
  obtain ⟨p, q, hpq, hpd, haq⟩ := exists_inverse_holder_exponents d hd a ha
  have hJ := memLp_japaneseDecay (d := d) a q hpq.symm.pos haq
  have hF := memLp_inverseFar (d := d) p hpd
  let B : ℝ := (∫ x : Mom d, ‖japaneseDecay a x‖ ^ q) ^ (1 / q) *
    (∫ x : Mom d, ‖inverseFar x‖ ^ p) ^ (1 / p)
  let C : ℝ := (∫ x : Mom d, inverseNear x) + B
  have ha0 : 0 ≤ a := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [ha, hdR]
  refine ⟨C, ?_, fun k => ?_⟩
  · exact add_nonneg (integral_nonneg inverseNear_nonneg)
      (mul_nonneg (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)
        (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _))
  · have hJn : Measurable (fun x : Mom d => japaneseDecay a (k + x)) := by
      have hb : Continuous (fun x : Mom d => 1 + ‖k + x‖ ^ 2) := by fun_prop
      exact (hb.rpow_const (fun _ => Or.inl (by positivity))).measurable
    have hN : Measurable (inverseNear : Mom d → ℝ) :=
      measurable_norm.inv.indicator measurableSet_ball
    have hnb (x : Mom d) : japaneseDecay a (k + x) * inverseNear x ≤ inverseNear x :=
      mul_le_of_le_one_left (inverseNear_nonneg x) (japaneseDecay_le_one ha0 _)
    have hiN : Integrable (fun x : Mom d => japaneseDecay a (k + x) * inverseNear x) := by
      refine (integrable_inverseNear hd).mono' (hJn.mul hN).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (japaneseDecay_nonneg a _) (inverseNear_nonneg x))]
      exact hnb x
    have hiF := integrable_translate_mul hpq.symm hJ hF k
    have hbF := integral_translate_mul_norm_le hpq.symm hJ hF k
    have he : (∫ x : Mom d, ‖japaneseDecay a (k + x)‖ * ‖inverseFar x‖) =
        ∫ x : Mom d, japaneseDecay a (k + x) * inverseFar x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [Real.norm_of_nonneg (japaneseDecay_nonneg a _),
          Real.norm_of_nonneg (inverseFar_nonneg x)]
    rw [he] at hbF
    have hsplit : (fun x : Mom d => japaneseDecay a (k + x) * ‖x‖⁻¹) =
        (fun x => japaneseDecay a (k + x) * inverseNear x +
          japaneseDecay a (k + x) * inverseFar x) := by
      funext x
      rw [← inverseNear_add_inverseFar x, mul_add]
    rw [hsplit]
    refine ⟨hiN.add hiF, ?_⟩
    rw [integral_add hiN hiF]
    exact add_le_add (integral_mono hiN (integrable_inverseNear hd) hnb) hbF

end WaveTurbulence.WKEL2
