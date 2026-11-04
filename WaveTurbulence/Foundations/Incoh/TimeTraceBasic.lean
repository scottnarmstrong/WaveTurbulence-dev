/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FrozenModulationMeasurable

/-!
# Smoothness, support and domination of fixed-clock traces

Only the approximations require smoothness; the common dominator is also
used for limits with hard time boundaries.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Incoh

@[fun_prop] theorem contDiff_updateTime {r : ℕ} (j : Fin r) (c : ℝ) :
    ContDiff ℝ ∞ (fun t : Fin r → ℝ => Function.update t j c) := by
  classical
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [Function.update_self] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin r → ℝ => c))
  · simpa only [Function.update_of_ne hi] using (show ContDiff ℝ ∞ (fun t : Fin r → ℝ => t i) from by fun_prop)

@[fun_prop] theorem contDiff_cutoffTimeTrace {r : ℕ} {χ : ℝ → ℝ} {F : (Fin r → ℝ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (j : Fin r) (c : ℝ) :
    ContDiff ℝ ∞ (cutoffTimeTrace χ j c F) :=
  (Fourier.coordinateCutoff_contDiff hχ).mul (hF.comp (contDiff_updateTime j c))

theorem hasCompactSupport_cutoffTimeTrace {r : ℕ} {χ : ℝ → ℝ} (hcχ : HasCompactSupport χ)
    (j : Fin r) (c : ℝ) (F : (Fin r → ℝ) → ℂ) : HasCompactSupport (cutoffTimeTrace χ j c F) :=
  (Fourier.coordinateCutoff_hasCompactSupport hcχ).mul_right

theorem norm_cutoffTimeTrace_le {r : ℕ} (χ : ℝ → ℝ) (j : Fin r) (c : ℝ)
    {F : (Fin r → ℝ) → ℂ} {M : ℝ} (hF : ∀ u, ‖F u‖ ≤ M) (t : Fin r → ℝ) :
    ‖cutoffTimeTrace χ j c F t‖ ≤ ‖Fourier.coordinateCutoff χ t‖ * M := by
  rw [cutoffTimeTrace, norm_mul]
  exact mul_le_mul_of_nonneg_left (hF _) (norm_nonneg _)

/-- The same time dominator applies uniformly to all frozen clock values. -/
theorem integrable_timeTrace_dominator {r : ℕ} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (M : ℝ) :
    Integrable (fun t : Fin r → ℝ => ‖Fourier.coordinateCutoff χ t‖ * M) :=
  (integrable_norm_coordinateCutoff hχ hcχ).mul_const M

end WaveTurbulence.Incoh
