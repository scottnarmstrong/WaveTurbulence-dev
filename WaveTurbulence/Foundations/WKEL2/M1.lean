/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AnisotropicConvolution
public import WaveTurbulence.Foundations.WKEL2.AnisotropicPolar
public import WaveTurbulence.Foundations.WKEL2.NonnegativeIntegral

/-!
# The uniform M₁ bound

Research-note Lemma 4(b). On unit vectors the transverse projection norm is
the absolute sine of the angle; the zero inverse convention is used on the
singular axis, as with the resonant measure's inverse norm.
-/

public section

noncomputable section

open MeasureTheory Metric

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Conversion of the nonnegative M₁ identity when its spatial integral is finite. -/
theorem integrable_M1_eq_of_integrable (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (ℓ k : Mom d)
    (hi : Integrable (fun u => japaneseDecay (2 * s) (k + u) * anisotropicKernel ℓ u)) :
    Integrable (fun v : sphere (0 : Mom d) 1 => radialWeight d s k v.1 * angularSineInv ℓ v.1)
      (volume : Measure (Mom d)).toSphere ∧
    (∫ v : sphere (0 : Mom d) 1, radialWeight d s k v.1 * angularSineInv ℓ v.1
      ∂(volume : Measure (Mom d)).toSphere) =
      ∫ u, japaneseDecay (2 * s) (k + u) * anisotropicKernel ℓ u := by
  have hm := (measurable_radialWeight_unitSphere s k).mul
    ((measurable_angularSineInv ℓ).comp measurable_subtype_coe)
  have hn (u : Mom d) : 0 ≤ japaneseDecay (2 * s) (k + u) * anisotropicKernel ℓ u :=
    mul_nonneg (japaneseDecay_nonneg _ _) (anisotropicKernel_nonneg _ _)
  apply integrable_integral_eq_of_lintegral_ofReal_eq hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v =>
      mul_nonneg (radialWeight_nonneg _ _ _ _) (angularSineInv_nonneg _ _))
    (integral_nonneg hn)
  exact ((ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)).trans
    (lintegral_anisotropic_eq_radialWeight hd s hs ℓ k)).symm

/-- Uniform M₁ bound, with a constant depending only on dimension and weight. -/
theorem exists_uniform_M1 (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : Mom d, ℓ ≠ 0 → ∀ k : Mom d,
      Integrable (fun v : sphere (0 : Mom d) 1 => radialWeight d s k v.1 * angularSineInv ℓ v.1)
        (volume : Measure (Mom d)).toSphere ∧
      (∫ v : sphere (0 : Mom d) 1, radialWeight d s k v.1 * angularSineInv ℓ v.1
        ∂(volume : Measure (Mom d)).toSphere) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_anisotropic_convolution hd s hs
  refine ⟨C, hC, fun ℓ hℓ k => ?_⟩
  obtain ⟨hiH, hbH⟩ := hbound ℓ hℓ k
  obtain ⟨hiA, heA⟩ := integrable_M1_eq_of_integrable hd s hs ℓ k hiH
  exact ⟨hiA, heA.le.trans hbH⟩

end WaveTurbulence.WKEL2
