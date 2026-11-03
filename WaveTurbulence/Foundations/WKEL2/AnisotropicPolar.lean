/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AnisotropicScaling
public import WaveTurbulence.Foundations.WKEL2.RadialWeightMeasure
public import WaveTurbulence.Foundations.WKEL2.PolarInverseSquare

/-!
# Polar identity for the M₁ angular kernel
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Spatial and angular forms of M₁ agree as nonnegative integrals. -/
theorem lintegral_anisotropic_eq_radialWeight (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (ℓ k : Mom d) :
    (∫⁻ u : Mom d, ENNReal.ofReal (japaneseDecay (2 * s) (k + u) * anisotropicKernel ℓ u)) =
      ∫⁻ v : sphere (0 : Mom d) 1,
        ENNReal.ofReal (radialWeight d s k v.1 * angularSineInv ℓ v.1)
        ∂(volume : Measure (Mom d)).toSphere := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; omega)
  have hJ : Continuous (fun u : Mom d => japaneseDecay (2 * s) (k + u)) := by
    have hb : Continuous (fun u : Mom d => 1 + ‖k + u‖ ^ 2) := by fun_prop
    exact hb.rpow_const (fun _ => Or.inl (by positivity))
  have hK : Measurable (anisotropicKernel ℓ) :=
    measurable_norm.inv.mul (measurable_angularSineInv ℓ)
  have hH : Measurable (fun u : Mom d =>
      ENNReal.ofReal (japaneseDecay (2 * s) (k + u) * anisotropicKernel ℓ u)) :=
    (hJ.measurable.mul hK).ennreal_ofReal
  rw [lintegral_polar volume hH]
  apply lintegral_congr
  intro v
  have hv : ‖(v : Mom d)‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hG : Measurable (fun r : Ioi (0 : ℝ) =>
      ENNReal.ofReal (japaneseDecay (2 * s) (k + r.1 • v.1))) :=
    (hJ.measurable.comp (continuous_subtype_val.smul continuous_const).measurable).ennreal_ofReal
  have hi : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1⁻¹)) :=
    measurable_subtype_coe.inv.ennreal_ofReal
  have hIIG : Measurable (fun r : Ioi (0 : ℝ) =>
      ENNReal.ofReal (r.1⁻¹) * ENNReal.ofReal (r.1⁻¹) *
        ENNReal.ofReal (japaneseDecay (2 * s) (k + r.1 • v.1))) :=
    (hi.mul hi).mul hG
  have hrewrite : (fun r : Ioi (0 : ℝ) => ENNReal.ofReal
      (japaneseDecay (2 * s) (k + r.1 • v.1) * anisotropicKernel ℓ (r.1 • v.1))) =
      (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (angularSineInv ℓ v.1) *
        (ENNReal.ofReal (r.1⁻¹) * ENNReal.ofReal (r.1⁻¹) *
          ENNReal.ofReal (japaneseDecay (2 * s) (k + r.1 • v.1)))) := by
    funext r
    rw [anisotropicKernel_pos_smul ℓ v.1 r.2, anisotropicKernel_of_norm_one ℓ v.1 hv,
      ENNReal.ofReal_mul (japaneseDecay_nonneg _ _),
      ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr r.2.le) (inv_nonneg.mpr r.2.le)),
      ENNReal.ofReal_mul (inv_nonneg.mpr r.2.le)]
    ac_rfl
  rw [hrewrite, finrank_euclideanSpace_fin,
    lintegral_const_mul (ENNReal.ofReal (angularSineInv ℓ v.1)) hIIG,
    show d - 1 = (d - 3) + 2 by omega,
    lintegral_volumeIoiPow_inv_sq (d - 3) hG,
    lintegral_radialWeight_measure hd s hs k v.1 hv,
    ← ENNReal.ofReal_mul (angularSineInv_nonneg _ _), mul_comm]

end WaveTurbulence.WKEL2
