/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AnisotropicSplit
public import WaveTurbulence.Foundations.WKEL2.AnisotropicExponent
public import WaveTurbulence.Foundations.WKEL2.HolderTranslation
public import WaveTurbulence.Foundations.WKEL2.WeightedKernelLp

/-!
# Uniform anisotropic convolution estimate

The spatial version of research-note Lemma 4(b), with a constant independent
of both translation and the distinguished axis.
-/

public section

noncomputable section

open MeasureTheory Set Metric

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Uniform spatial M₁ bound in the sharp open weighted-L² range. -/
theorem exists_uniform_anisotropic_convolution (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : Mom d, ℓ ≠ 0 → ∀ k : Mom d,
      Integrable (fun u => japaneseDecay (2 * s) (k + u) * anisotropicKernel ℓ u) ∧
      (∫ u, japaneseDecay (2 * s) (k + u) * anisotropicKernel ℓ u) ≤ C := by
  obtain ⟨p, q, hpq, hpdim, hphi, hsqp⟩ := exists_anisotropic_holder_exponents d hd s hs
  have hJ := memLp_japaneseDecay (d := d) (2 * s) q hpq.symm.pos hsqp
  let B : ℝ := (∫ x : Mom d, ‖japaneseDecay (2 * s) x‖ ^ q) ^ (1 / q) *
    (∫ z : ℝ × Mom (d - 1), ‖(ball 0 1)ᶜ.indicator (axisKernel 1) z‖ ^ p
      ∂volume.prod volume) ^ (1 / p)
  let N : ℝ := ∫ z : ℝ × Mom (d - 1), (ball 0 1).indicator (axisKernel 1) z ∂volume.prod volume
  have hs0 : 0 ≤ 2 * s := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hs, hdR]
  refine ⟨N + B, ?_, fun ℓ hℓ k => ?_⟩
  · exact add_nonneg (integral_nonneg fun _ => indicator_nonneg (fun x _ => axisKernel_nonneg 1 x) _)
      (mul_nonneg (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)
        (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _))
  · have hF := memLp_anisotropicFar hd hℓ p hpdim hphi
    have hiF := integrable_translate_mul hpq.symm hJ hF k
    have hbF := integral_translate_mul_norm_le hpq.symm hJ hF k
    have hJn : Measurable (fun u : Mom d => japaneseDecay (2 * s) (k + u)) := by
      have hb : Continuous (fun u : Mom d => 1 + ‖k + u‖ ^ 2) := by fun_prop
      exact (hb.rpow_const (fun _ => Or.inl (by positivity))).measurable
    have hnb (u : Mom d) :
        japaneseDecay (2 * s) (k + u) * anisotropicNear hℓ u ≤ anisotropicNear hℓ u :=
      mul_le_of_le_one_left (anisotropicNear_nonneg hℓ u) (japaneseDecay_le_one hs0 _)
    have hiN : Integrable (fun u : Mom d => japaneseDecay (2 * s) (k + u) * anisotropicNear hℓ u) := by
      refine (integrable_anisotropicNear hd hℓ).mono'
        (hJn.mul (measurable_anisotropicNear hℓ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => ?_)
      rw [Real.norm_of_nonneg
        (mul_nonneg (japaneseDecay_nonneg _ _) (anisotropicNear_nonneg hℓ u))]
      exact hnb u
    have heF : (∫ u : Mom d, ‖japaneseDecay (2 * s) (k + u)‖ * ‖anisotropicFar hℓ u‖) =
        ∫ u : Mom d, japaneseDecay (2 * s) (k + u) * anisotropicFar hℓ u := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        dsimp only
        rw [Real.norm_of_nonneg (japaneseDecay_nonneg _ _),
          Real.norm_of_nonneg (anisotropicFar_nonneg hℓ u)]
    rw [heF, integral_anisotropicFar_norm_rpow hℓ p] at hbF
    have heN := (integral_mono hiN (integrable_anisotropicNear hd hℓ) hnb).trans_eq
      (integral_anisotropicNear hℓ)
    have hsplit : (fun u : Mom d => japaneseDecay (2 * s) (k + u) * anisotropicKernel ℓ u) =
        (fun u => japaneseDecay (2 * s) (k + u) * anisotropicNear hℓ u +
          japaneseDecay (2 * s) (k + u) * anisotropicFar hℓ u) := by
      funext u
      rw [← anisotropicNear_add_anisotropicFar hℓ u, mul_add]
    rw [hsplit]
    refine ⟨hiN.add hiF, ?_⟩
    rw [integral_add hiN hiF]
    exact add_le_add heN hbF

end WaveTurbulence.WKEL2
