/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PhaseMeasurability
public import WaveTurbulence.Foundations.Sumint.TimeExitMeasurability
public import WaveTurbulence.Foundations.Sumint.ExponentialBoxMass
public import WaveTurbulence.Foundations.Sumint.FourierFubini

/-!
# Rectangular extensions for general input coefficients

This auxiliary operator permits summing the spatial lattice variables
before estimating the input-time integral. Its hypotheses concern only
measurability and integrability of the input coefficient. They do not
assert any of the source oscillatory estimates.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Sumint

/-- The explicit rectangular extension of an arbitrary input coefficient. -/
@[expose] noncomputable def kernelExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ) (z : Fin 3 → ℝ) : ℂ :=
  ∫ u in localInputTimeDomain D c h, F u * exponentialBox (lowerTimeExit D hI u)
    (upperTimeExit D hI u) (u (firstTime D hI)) z

/-- A measurable integrable input coefficient gives product integrability
for the complete rectangular extension integrand. -/
theorem integrable_kernelExtension_integrand {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (hFm : Measurable F) (hFi : IntegrableOn F (localInputTimeDomain D c h)) :
    Integrable (fun p : (D.S.TVar → ℝ) × (Fin 3 → ℝ) => F p.1 *
      exponentialBox (lowerTimeExit D hI p.1) (upperTimeExit D hI p.1)
        (p.1 (firstTime D hI)) p.2)
      ((volume.restrict (localInputTimeDomain D c h)).prod volume) := by
  apply integrable_mul_kernel F
    (fun u z => exponentialBox (lowerTimeExit D hI u) (upperTimeExit D hI u)
      (u (firstTime D hI)) z) hFi
  · exact ((hFm.comp measurable_fst).mul
      (measurable_exit_exponentialBox D hI)).aestronglyMeasurable
  · exact ae_of_all _ (fun _ => integrable_exponentialBox _ _ _)
  · filter_upwards [ae_restrict_mem (measurableSet_localInputTimeDomain D c h)] with u hu
    have hn : ∀ v, u v ≤ 0 := fun v => (hu.2.1 v).le
    exact integral_norm_exponentialBox_le_all (lowerTimeExit_nonneg D hI u hn)
      (hn (firstTime D hI))

/-- The general extension satisfies the ambient integrability guard. -/
theorem integrable_kernelExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (hFm : Measurable F) (hFi : IntegrableOn F (localInputTimeDomain D c h)) :
    Integrable (kernelExtension D hI c h F) :=
  (integrable_kernelExtension_integrand D hI c h F hFm hFi).integral_prod_right

/-- Fourier Fubini retains the whole input coefficient, including spatial
cancellation already performed inside it. -/
theorem timeFourier_kernelExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (hFm : Measurable F) (hFi : IntegrableOn F (localInputTimeDomain D c h))
    (ξ : Fin 3 → ℝ) :
    Fourier.timeFourier (kernelExtension D hI c h F) ξ =
      ∫ u in localInputTimeDomain D c h, F u *
        Fourier.timeFourier (exponentialBox (lowerTimeExit D hI u)
          (upperTimeExit D hI u) (u (firstTime D hI))) ξ := by
  unfold kernelExtension
  rw [timeFourier_integral _ (integrable_kernelExtension_integrand D hI c h F hFm hFi)]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  exact congrFun (Fourier.timeFourier_smul (F u)
    (exponentialBox (lowerTimeExit D hI u) (upperTimeExit D hI u)
      (u (firstTime D hI)))) ξ

/-- Uniform Fourier decay with the absolute input coefficient mass retained. -/
theorem norm_timeFourier_kernelExtension_le {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (hFm : Measurable F) (hFi : IntegrableOn F (localInputTimeDomain D c h))
    (ξ : Fin 3 → ℝ) :
    ‖Fourier.timeFourier (kernelExtension D hI c h F) ξ‖ ≤
      (∫ u in localInputTimeDomain D c h, ‖F u‖) * (2 * ∏ j, 1/scalarBracket (ξ j)) := by
  rw [timeFourier_kernelExtension D hI c h F hFm hFi ξ]
  calc
    _ ≤ ∫ u in localInputTimeDomain D c h, ‖F u‖ * (2 * ∏ j, 1/scalarBracket (ξ j)) := by
      apply norm_integral_le_of_norm_le (hFi.norm.mul_const _)
      filter_upwards [ae_restrict_mem (measurableSet_localInputTimeDomain D c h)] with u hu
      rw [norm_mul]
      have hn : ∀ v, u v ≤ 0 := fun v => (hu.2.1 v).le
      exact mul_le_mul_of_nonneg_left
        (norm_timeFourier_exponentialBox_le_all (lowerTimeExit_nonneg D hI u hn)
          (hn (firstTime D hI)) ξ) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

end WaveTurbulence.Sumint
