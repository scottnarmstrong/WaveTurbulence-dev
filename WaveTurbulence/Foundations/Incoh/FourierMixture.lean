/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier transforms of actual kernel mixtures

Fubini commutes the Fourier transform with the remaining internal-clock
integral. Joint integrability is a typing premise, not a norm estimate.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Fourier transformation commutes with an integrable parameter mixture. -/
theorem timeFourier_integral_mixture {r : ℕ} {U W : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (A : U → ℂ) (p : U → W)
    (K : (Fin r → ℝ) → W → ℂ)
    (h : Integrable (fun z : (Fin r → ℝ) × U => A z.2 * K z.1 (p z.2)) (volume.prod μ))
    (ξ : Fin r → ℝ) :
    Fourier.timeFourier (fun t => ∫ u, A u * K t (p u) ∂μ) ξ =
      ∫ u, A u * Fourier.timeFourier (fun t => K t (p u)) ξ ∂μ := by
  let P : (Fin r → ℝ) → ℂ := fun t => Real.fourierChar (-Fourier.timePairing r t ξ)
  have hc : Continuous P := by
    unfold P
    apply continuous_subtype_val.comp
    apply Real.continuous_fourierChar.comp
    change Continuous (fun t : Fin r → ℝ => -(∑ j, t j * ξ j))
    fun_prop
  have hi : Integrable (fun z : (Fin r → ℝ) × U => P z.1 * (A z.2 * K z.1 (p z.2)))
      (volume.prod μ) := by
    have hp : AEStronglyMeasurable (fun z : (Fin r → ℝ) × U => P z.1) (volume.prod μ) :=
      hc.measurable.comp measurable_fst |>.aestronglyMeasurable
    simpa only [mul_comm] using h.mul_bdd hp (Filter.Eventually.of_forall (fun z => by
      simp only [P, Circle.norm_coe]; exact le_rfl))
  change (∫ t, P t * (∫ u, A u * K t (p u) ∂μ)) =
    ∫ u, A u * (∫ t, P t * K t (p u)) ∂μ
  calc
    _ = ∫ t, ∫ u, P t * (A u * K t (p u)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => (integral_const_mul _ _).symm)
    _ = ∫ u, (∫ t, P t * (A u * K t (p u))) ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by ring))

end WaveTurbulence.Incoh
