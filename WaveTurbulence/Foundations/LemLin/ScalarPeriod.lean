/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarFinite
public import WaveTurbulence.Foundations.LemLin.Periodization

/-!
# One-period L¹ bound for the scalar cutoff sum

The cancellation step of TARGET `lemlin`, L1541–L1543. The constant is the
Fourier L¹ norm of the fixed scalar cutoff, independent of translation,
frequency, and the location of the integration interval.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set
open scoped FourierTransform ENNReal

/-- The Fourier transform of the fixed scalar cutoff is integrable. -/
theorem integrable_fourier_chi0Complex : Integrable (𝓕 Fourier.chi0Complex) := by
  have heq : (scalarAmplitudeSchwartz 0 0 : ℝ → ℂ) = Fourier.chi0Complex := by
    funext x
    simp only [scalarAmplitudeSchwartz_apply, scalarAmplitude, sub_zero, neg_zero,
      zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  have hi := (𝓕 (scalarAmplitudeSchwartz 0 0)).integrable (μ := volume)
  change Integrable (𝓕 (scalarAmplitudeSchwartz 0 0 : ℝ → ℂ)) at hi
  rwa [heq] at hi

theorem continuous_fourier_chi0Complex : Continuous (𝓕 Fourier.chi0Complex) := by
  change Continuous (fun u => 𝓕 Fourier.chi0Complex u)
  simp_rw [Real.fourier_eq]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂
    (Fourier.chi0Complex_contDiff.continuous.integrable_of_hasCompactSupport
      (Fourier.chi0_hasCompactSupport.comp_left Complex.ofReal_zero))

/-- The fixed Fourier L¹ mass appearing in the cancellation estimate. -/
@[expose] noncomputable def scalarFourierMass : ℝ := ∫ u : ℝ, ‖𝓕 Fourier.chi0Complex u‖

theorem scalarFourierMass_nonneg : 0 ≤ scalarFourierMass :=
  integral_nonneg (fun _ => norm_nonneg _)

/-- TARGET `lemlin`: one frequency period has mass at most `L` times the fixed Fourier mass. -/
theorem integral_scalarLatticeSum_period {L : ℝ} (hL : 0 < L) (a τ : ℝ) :
    (∫ u in Ioc τ (τ + L), ‖scalarLatticeSum L a u‖) ≤ L * scalarFourierMass := by
  have hs : IntegrableOn (fun u => ‖scalarLatticeSum L a u‖) (Ioc τ (τ + L)) :=
    ((continuous_scalarLatticeSum hL a).norm.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hm : AEMeasurable
      (fun u => ∑' n : ℤ, ENNReal.ofReal ‖𝓕 Fourier.chi0Complex (u + L * n)‖)
      (volume.restrict (Ioc τ (τ + L))) := by
    apply AEMeasurable.tsum
    intro n
    exact (continuous_fourier_chi0Complex.comp
      (continuous_id.add continuous_const)).norm.aemeasurable.restrict.ennreal_ofReal
  have hp := lintegral_periodization integrable_fourier_chi0Complex.norm
    (fun u => norm_nonneg _) hL τ
  have he : ENNReal.ofReal (∫ u in Ioc τ (τ + L), ‖scalarLatticeSum L a u‖) ≤
      ENNReal.ofReal (L * scalarFourierMass) := by
    rw [ofReal_integral_eq_lintegral_ofReal hs (ae_of_all _ (fun u => norm_nonneg _))]
    calc
      _ ≤ ∫⁻ u in Ioc τ (τ + L), ENNReal.ofReal L *
          ∑' n : ℤ, ENNReal.ofReal ‖𝓕 Fourier.chi0Complex (u + L * n)‖ :=
        lintegral_mono (fun u => enorm_scalarLatticeSum_le hL a u)
      _ = ENNReal.ofReal L * ENNReal.ofReal scalarFourierMass := by
        rw [lintegral_const_mul'' _ hm, hp]
        rfl
      _ = _ := (ENNReal.ofReal_mul hL.le).symm
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL.le scalarFourierMass_nonneg)).mp he

end WaveTurbulence.LemLin
