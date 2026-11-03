/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Cutoff Duhamel modes

DNY21, Lemma 3.1 (`lin`, L392), and TARGET L2365: the scalar Fourier kernel
is the transform of a cutoff primitive of a single Fourier mode. We use
`exp(2π i σt)` for the input mode, consistently with `timeFourier`.
-/

public section

open MeasureTheory
open scoped FourierTransform ContDiff

namespace WaveTurbulence.Fourier

/-- The primitive of a cutoff Fourier mode, based at zero. -/
@[expose] noncomputable def duhamelPrimitive (χ : ℝ → ℝ) (σ t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..t, (χ u : ℂ) * (Real.fourierChar (σ * u) : ℂ)

/-- The scalar output mode of the cutoff Duhamel operator. -/
@[expose] noncomputable def duhamelMode (χ : ℝ → ℝ) (σ t : ℝ) : ℂ :=
  (χ t : ℂ) * duhamelPrimitive χ σ t

/-- The one-dimensional DNY21 kernel in the paper's Fourier convention. -/
@[expose] noncomputable def duhamelKernel (χ : ℝ → ℝ) (ξ σ : ℝ) : ℂ :=
  𝓕 (duhamelMode χ σ) ξ

/-- Fundamental theorem of calculus for the mode primitive. -/
theorem hasDerivAt_duhamelPrimitive {χ : ℝ → ℝ} (hχ : Continuous χ) (σ t : ℝ) :
    HasDerivAt (duhamelPrimitive χ σ)
      ((χ t : ℂ) * (Real.fourierChar (σ * t) : ℂ)) t := by
  have hc : Continuous (fun u : ℝ => (χ u : ℂ) * (Real.fourierChar (σ * u) : ℂ)) := by
    fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Smoothness of the primitive follows from smoothness of its derivative. -/
theorem duhamelPrimitive_contDiff {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (σ : ℝ) :
    ContDiff ℝ ∞ (duhamelPrimitive χ σ) := by
  have hd := fun t => hasDerivAt_duhamelPrimitive hχ.continuous σ t
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  have he : deriv (duhamelPrimitive χ σ) =
      fun t => (χ t : ℂ) * (Real.fourierChar (σ * t) : ℂ) := funext fun t => (hd t).deriv
  rw [he]
  change ContDiff ℝ ∞ (fun t => (χ t : ℂ) *
    Complex.exp ((2 * Real.pi * (σ * t) : ℝ) * Complex.I))
  have hl : ContDiff ℝ ∞ (fun t : ℝ => 2 * Real.pi * (σ * t)) := by fun_prop
  have hi : ContDiff ℝ ∞ (fun _ : ℝ => Complex.I) := contDiff_const
  exact (Complex.ofRealCLM.contDiff.comp hχ).mul
    (((Complex.ofRealCLM.contDiff.comp hl).mul hi).cexp)

/-- The primitive is bounded uniformly in the input frequency. -/
theorem norm_duhamelPrimitive_le {χ : ℝ → ℝ} (hχ : Integrable χ) (σ t : ℝ) :
    ‖duhamelPrimitive χ σ t‖ ≤ ∫ u, |χ u| := by
  calc
    _ ≤ ∫ u in Set.uIoc 0 t, |χ u| := by
      simpa only [duhamelPrimitive, norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc
          (f := fun u => (χ u : ℂ) * (Real.fourierChar (σ * u) : ℂ)) (a := 0) (b := t))
    _ ≤ _ := integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun u => abs_nonneg (χ u)) hχ.norm

/-- The scalar kernel has a uniform bound before frequency weights are inserted. -/
theorem norm_duhamelKernel_le {χ : ℝ → ℝ} (hχ : Integrable χ) (ξ σ : ℝ) :
    ‖duhamelKernel χ ξ σ‖ ≤ (∫ u, |χ u|) ^ 2 := by
  apply (Real.norm_fourier_le_integral_norm (duhamelMode χ σ) ξ).trans
  calc
    (∫ t, ‖duhamelMode χ σ t‖) ≤ ∫ t, |χ t| * (∫ u, |χ u|) := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        (hχ.norm.mul_const _) (ae_of_all _ fun t => ?_)
      simp only [duhamelMode, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_duhamelPrimitive_le hχ σ t) (abs_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

/-- A smooth cutoff gives a smooth output mode. -/
theorem duhamelMode_contDiff {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (σ : ℝ) :
    ContDiff ℝ ∞ (duhamelMode χ σ) :=
  (Complex.ofRealCLM.contDiff.comp hχ).mul (duhamelPrimitive_contDiff hχ σ)

/-- Multiplication by the outer cutoff keeps the output mode compactly supported. -/
theorem duhamelMode_hasCompactSupport {χ : ℝ → ℝ} (hχ : HasCompactSupport χ) (σ : ℝ) :
    HasCompactSupport (duhamelMode χ σ) := by
  have hc : HasCompactSupport (fun t => (χ t : ℂ)) :=
    hχ.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  exact hc.mul_right

end WaveTurbulence.Fourier
