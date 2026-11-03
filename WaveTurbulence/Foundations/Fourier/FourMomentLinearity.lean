/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourTimeMoments
import Mathlib.Tactic

/-!
# Additivity and triangle inequalities for endpoint moments

The four derivative moments are subadditive on smooth functions. This
allows the three diagonal product-rule terms to be estimated separately.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The frozen partial derivative is additive on smooth inputs. -/
theorem partialDeriv_add_smooth {r : ℕ} {f g : (Fin r → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : Fin r) :
    WaveTurbulence.partialDeriv j (fun x => f x + g x) =
      fun x => WaveTurbulence.partialDeriv j f x + WaveTurbulence.partialDeriv j g x := by
  have hfg : ContDiff ℝ ∞ (fun x => f x + g x) := by
    convert hf.add hg using 1
  rw [WaveTurbulence.partialDeriv_eq_fderiv_fun (hfg.differentiable (by simp)) j,
    WaveTurbulence.partialDeriv_eq_fderiv_fun (hf.differentiable (by simp)) j,
    WaveTurbulence.partialDeriv_eq_fderiv_fun (hg.differentiable (by simp)) j]
  funext x
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x), add_apply]

/-- Every one of the four endpoint derivatives is additive. -/
theorem fourTimeDerivatives_add {f g : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : Fin 4) :
    fourTimeDerivatives (fun t => f t + g t) j =
      fun t => fourTimeDerivatives f j t + fourTimeDerivatives g j t := by
  fin_cases j
  · rfl
  · exact partialDeriv_add_smooth hf hg 0
  · exact partialDeriv_add_smooth hf hg 1
  · change WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 (fun t => f t + g t)) = _
    rw [partialDeriv_add_smooth hf hg 1]
    exact partialDeriv_add_smooth (WaveTurbulence.contDiff_infty_partialDeriv hf 1)
      (WaveTurbulence.contDiff_infty_partialDeriv hg 1) 0

/-- Smoothness of every endpoint derivative. -/
theorem fourTimeDerivatives_contDiff {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : Fin 4) : ContDiff ℝ ∞ (fourTimeDerivatives f j) := by
  fin_cases j
  · exact hf
  · exact WaveTurbulence.contDiff_infty_partialDeriv hf 0
  · exact WaveTurbulence.contDiff_infty_partialDeriv hf 1
  · exact WaveTurbulence.contDiff_infty_partialDeriv
      (WaveTurbulence.contDiff_infty_partialDeriv hf 1) 0

/-- The time `L¹` triangle inequality, with a measurable first summand. -/
theorem lintegral_enorm_add_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : Measurable f) :
    (∫⁻ t, ‖f t + g t‖ₑ ∂μ) ≤ (∫⁻ t, ‖f t‖ₑ ∂μ) + ∫⁻ t, ‖g t‖ₑ ∂μ := by
  exact (lintegral_mono (fun t => enorm_add_le (f t) (g t))).trans_eq (lintegral_add_left hf.enorm _)

/-- The corresponding triangle inequality for subtraction. -/
theorem lintegral_enorm_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : Measurable f) :
    (∫⁻ t, ‖f t - g t‖ₑ ∂μ) ≤ (∫⁻ t, ‖f t‖ₑ ∂μ) + ∫⁻ t, ‖g t‖ₑ ∂μ := by
  exact (lintegral_mono (fun _ => enorm_sub_le)).trans_eq (lintegral_add_left hf.enorm _)

/-- Subadditivity of the sum of the four actual endpoint moments. -/
theorem fourTimeMomentNorm_add_le {f g : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    fourTimeMomentNorm (fun t => f t + g t) ≤ fourTimeMomentNorm f + fourTimeMomentNorm g := by
  unfold fourTimeMomentNorm
  calc
    _ ≤ ∑ j : Fin 4, ((∫⁻ t, ‖fourTimeDerivatives f j t‖ₑ) +
        ∫⁻ t, ‖fourTimeDerivatives g j t‖ₑ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [fourTimeDerivatives_add hf hg j]
      exact lintegral_enorm_add_le (fourTimeDerivatives_contDiff hf j).continuous.measurable
    _ = _ := Finset.sum_add_distrib

end WaveTurbulence.Fourier
