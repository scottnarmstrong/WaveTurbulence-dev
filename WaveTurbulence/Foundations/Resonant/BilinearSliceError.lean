/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.BilinearFourierLimit
public import WaveTurbulence.Foundations.Resonant.SymmetricQuotient
public import WaveTurbulence.Foundations.Resonant.FourierPhase

/-!
# Quantitative small-energy error on a bilinear slice

The symmetric quotient of the test function times its Fourier phase is
bounded by a constant linear in the normal frequency. The low-energy cutoff
has `L¹` norm proportional to its inverse scale, giving the `μ⁻¹` error in
DH21 Lemma 6.3(2).
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- The small-energy error, before replacing the hyperplane volume by a radius power. -/
theorem norm_bilinearInvFourierInner_error_le_volume
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) {μ R : ℝ} {D : ℝ≥0}
    (hμ : 0 < μ) (hR : 0 < R) {f : Mom d → ℂ} {b : Mom d}
    (hL : LipschitzWith D f) (hs : ∀ y, R < ‖y - b‖ → f y = 0)
    (hb : ∀ y, ‖f y‖ ≤ D) {ℓ : Mom d} (hℓ : ℓ ≠ 0) (η : Mom d) :
    ‖bilinearSliceLimitFormula f ℓ η - bilinearInvFourierInner χ μ f ℓ η‖ ≤
      μ⁻¹ * (‖ℓ‖⁻¹) ^ 2 *
        ((D : ℝ) * volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R)) *
          (1 + ‖η‖) * ∫ u : ℝ, |χ u|) := by
  let ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ := fun w => unitPhase 1 ⟪η, (w : Mom d)⟫_ℝ
  let s : ℝ → ℂ := localizedSlice f ψ
  let ν : ℝ := ⟪η, unitVec ℓ⟫_ℝ
  let K : ℝ≥0 := ⟨(D : ℝ) * volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R)),
    mul_nonneg D.coe_nonneg ENNReal.toReal_nonneg⟩
  have hψc : Continuous ψ :=
    (continuous_unitPhase 1).comp (continuous_const.inner continuous_subtype_val)
  have hψ : ∀ w, ‖ψ w‖ ≤ 1 := fun _ => (norm_unitPhase 1 _).le
  have hsi : Integrable s := integrable_localizedSlice hL.continuous hs hℓ hψc hψ
  have hsl : LipschitzWith K s := lipschitzWith_localizedSlice hR hL hs hb hℓ hψc hψ
  have hsb : ∀ t, ‖s t‖ ≤ K := fun t => norm_localizedSlice_le hR hs hb hℓ hψ t
  let g : ℝ → ℂ := fun t => s t * unitPhase ν t
  have hgi : Integrable g := hsi.mul_bdd (c := 1) (continuous_unitPhase ν).aestronglyMeasurable
    (Eventually.of_forall fun t => (norm_unitPhase ν t).le)
  have hgl : LipschitzWith (K + K * ⟨|ν|, abs_nonneg ν⟩) g := lipschitzWith_mul_unitPhase hsl hsb ν
  have hlim1 := tendsto_pvFourierTruncation_of_lipschitz hχ hsi hsl ν
  have hlim2 := tendsto_pvTruncationComplex_of_lipschitz hχ hgi hgl
  have hvalue : bilinearSliceLimitFormula f ℓ η =
      ((‖ℓ‖⁻¹ : ℝ) : ℂ) * ∫ u : ℝ, symmetricQuotient g u := by
    have he := tendsto_nhds_unique hlim1 hlim2
    change ((‖ℓ‖⁻¹ : ℝ) : ℂ) *
      ((∫ u : ℝ, pvRemainder s u * unitPhase ν u) +
        s 0 * (2 * Complex.I * (∫ t in (0 : ℝ)..1, ν * Real.sinc (ν * t) : ℝ))) = _
    rw [he]
  rw [hvalue, bilinearInvFourierInner_eq hχ μ hL.continuous hs hℓ η]
  change ‖((‖ℓ‖⁻¹ : ℝ) : ℂ) * (∫ u : ℝ, symmetricQuotient g u) -
    ((‖ℓ‖⁻¹ : ℝ) : ℂ) * pvTruncationComplex χ (μ * ‖ℓ‖) g‖ ≤ _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  have hscale : 0 < μ * ‖ℓ‖ := mul_pos hμ (norm_pos_iff.mpr hℓ)
  have he := norm_pvTruncationComplex_error_le hχ hgi hgl hscale
  change ‖(∫ u : ℝ, symmetricQuotient g u) - pvTruncationComplex χ (μ * ‖ℓ‖) g‖ ≤
    ((K : ℝ) + (K : ℝ) * |ν|) * (μ * ‖ℓ‖)⁻¹ * ∫ u : ℝ, |χ u| at he
  have hν : |ν| ≤ ‖η‖ := by
    simpa only [ν, norm_unitVec hℓ, mul_one] using abs_real_inner_le_norm η (unitVec ℓ)
  have hK : (K : ℝ) + (K : ℝ) * |ν| ≤
      ((D : ℝ) * volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R))) * (1 + ‖η‖) := by
    have hh := add_le_add (le_refl (K : ℝ)) (mul_le_mul_of_nonneg_left hν K.coe_nonneg)
    exact hh.trans_eq (by change (K : ℝ) + (K : ℝ) * ‖η‖ = (K : ℝ) * (1 + ‖η‖); ring)
  have hiχ : 0 ≤ ∫ u : ℝ, |χ u| := integral_nonneg fun _ => abs_nonneg _
  have hh := he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (inv_nonneg.mpr hscale.le)) hiχ)
  refine (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (norm_nonneg _))).trans_eq ?_
  rw [mul_inv]
  ring

end WaveTurbulence.Resonant
