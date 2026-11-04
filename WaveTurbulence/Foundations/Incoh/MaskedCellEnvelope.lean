/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MaskedSourceDerivativeBound
public import WaveTurbulence.Foundations.Incoh.WeightedSpectralMomentMass
public import WaveTurbulence.Foundations.Incoh.SpectralMomentContinuity
public import WaveTurbulence.Foundations.Incoh.SourceCellMeasure

/-! # Actual counted spectral envelopes for full source spatial norms -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The explicit weighted derivative coefficient is nonnegative. -/
theorem maskedSourceSpatialConstant_nonneg (d m J W : ℕ) : 0 ≤ maskedSourceSpatialConstant d m J W := by
  unfold maskedSourceSpatialConstant
  have hD : 0 ≤ rootMaskDerivativeConstant d J := zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)
  positivity

/-- Literal actual higher-moment envelope over the selected source cells and spectral variables. -/
@[expose] def maskedCellEnvelope {d n m : ℕ} (J W : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ℝ :=
  maskedSourceSpatialConstant d m J W *
    (∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (u.1.1 a)) ^ W) *
      ‖localizedSpectralMomentReference J f u.1.1 u.2‖

theorem maskedCellEnvelope_nonneg {d n m : ℕ} (J W : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : 0 ≤ maskedCellEnvelope J W f S u := by
  unfold maskedCellEnvelope
  exact mul_nonneg (mul_nonneg (maskedSourceSpatialConstant_nonneg _ _ _ _)
    (Finset.prod_nonneg (fun a _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W))) (norm_nonneg _)

/-- Measurability of the actual counted derivative envelope follows from the source inputs. -/
theorem measurable_maskedCellEnvelope {d n m K M : ℕ} (J W : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) {B : ℝ}
    (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    Measurable (maskedCellEnvelope J W f S) := by
  apply measurable_from_prod_countable_right
  intro u
  change Measurable (fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
    (maskedSourceSpatialConstant d m J W *
      ∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (u.1 a)) ^ W) *
        ‖localizedSpectralMomentReference J f u.1 ξ‖)
  exact (continuous_const.mul (continuous_localizedSpectralMomentReference J f u.1 hK hB h).norm).measurable

/-- Actual counted weighted derivative envelopes have the required finite exponential mass. -/
theorem lintegral_maskedCellEnvelope_le {d n m K M : ℕ} (J W : ℕ)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hM : W + 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∫⁻ u, ENNReal.ofReal (maskedCellEnvelope J W f S u) ∂sourceCellMeasure S) ≤
      ENNReal.ofReal (maskedSourceSpatialConstant d m J W) * ENNReal.ofReal (C ^ n) *
        (ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W * B) ^ m *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)) := by
  let E := fun c : Fin m → Fin d → ℤ => fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
    ENNReal.ofReal (∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) ^ W) *
      ‖localizedSpectralMomentReference J f c ξ‖ₑ
  have hm (c : Fin m → Fin d → ℤ) : Measurable (E c) :=
    measurable_const.mul (continuous_localizedSpectralMomentReference J f c (by omega) hB h).measurable.enorm
  have hE : Measurable (fun u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ) => E u.1.1 u.2) :=
    measurable_from_prod_countable_right (fun u => hm u.1)
  have he (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) :
      ENNReal.ofReal (maskedCellEnvelope J W f S u) =
        ENNReal.ofReal (maskedSourceSpatialConstant d m J W) * E u.1.1 u.2 := by
    simp only [maskedCellEnvelope, E, ENNReal.ofReal_mul (maskedSourceSpatialConstant_nonneg _ _ _ _),
      ENNReal.ofReal_mul (Finset.prod_nonneg (fun a _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)),
      ← ofReal_norm, mul_assoc]
  simp_rw [he]
  rw [lintegral_const_mul _ hE, lintegral_sourceCellMeasure S E hm, mul_assoc]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∑' c : Fin m → Fin d → ℤ, ENNReal.ofReal (C ^ n) * ∫⁻ ξ, E c ξ := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply mul_le_mul' _ le_rfl
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hS c)
    _ = ENNReal.ofReal (C ^ n) * ∑' c : Fin m → Fin d → ℤ, ∫⁻ ξ, E c ξ := ENNReal.tsum_mul_left
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      have heint (c : Fin m → Fin d → ℤ) : (∫⁻ ξ, E c ξ) =
          ENNReal.ofReal (∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) ^ W) *
            ∫⁻ ξ, ‖localizedSpectralMomentReference (n := n) J f c ξ‖ₑ :=
        lintegral_const_mul _ (continuous_localizedSpectralMomentReference J f c (by omega) hB h).measurable.enorm
      simp_rw [heint]
      exact tsum_weighted_lintegral_enorm_localizedSpectralMomentReference_le J f hK hM hB h

end WaveTurbulence.Incoh
