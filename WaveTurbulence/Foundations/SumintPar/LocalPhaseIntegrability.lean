/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PhaseMeasurability
public import WaveTurbulence.Foundations.SumintPar.TimeExitMeasurability
public import WaveTurbulence.Foundations.SumintPar.ExponentialBoxMass
public import WaveTurbulence.Foundations.SumintPar.KernelIntegrability

/-!
# The explicit local phase extension satisfies the ambient norm guard

Fubini applies to the literal phase and rectangular kernel on the fixed
local input domain. No regularity in momentum is required.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

/-- The complete local phase/kernel integrand is integrable on the product space. -/
theorem integrable_phase_exit_kernel {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (hη : η ≤ 1/3) (x : D.S.VIdx → Fin d → ℤ)
    (r : Mom d) (c h : ℝ) :
    Integrable (fun p : (D.S.TVar → ℝ) × (Fin 3 → ℝ) =>
      D.phase L γ δ η x r 0 p.1 * exponentialBox (lowerTimeExit D hI p.1)
        (upperTimeExit D hI p.1) (p.1 (firstTime D hI)) p.2)
      ((volume.restrict (localInputTimeDomain D c h)).prod volume) := by
  apply integrable_mul_kernel (D.phase L γ δ η x r 0)
    (fun u z => exponentialBox (lowerTimeExit D hI u) (upperTimeExit D hI u)
      (u (firstTime D hI)) z)
    (integrableOn_phase_localDomain D L γ δ η hη x r 0 c h)
  · exact (((measurable_phase D L γ δ η x r 0).comp measurable_fst).mul
      (measurable_exit_exponentialBox D hI)).aestronglyMeasurable
  · exact ae_of_all _ (fun u => integrable_exponentialBox _ _ _)
  · filter_upwards [ae_restrict_mem (measurableSet_localInputTimeDomain D c h)] with u hu
    have hn : ∀ v, u v ≤ 0 := fun v => (hu.2.1 v).le
    exact integral_norm_exponentialBox_le_all (lowerTimeExit_nonneg D hI u hn)
      (hn (firstTime D hI))

/-- Each local phase extension is a genuinely integrable function of the three output times. -/
theorem integrable_localPhaseExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (hη : η ≤ 1/3) (x : D.S.VIdx → Fin d → ℤ)
    (r : Mom d) (c h : ℝ) :
    Integrable (localPhaseExtension D hI L γ δ η x r c h) := by
  exact (integrable_phase_exit_kernel D hI L γ δ η hη x r c h).integral_prod_right

end WaveTurbulence.SumintPar
