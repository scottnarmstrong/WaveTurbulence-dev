/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.DuhamelKernelBound
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Tactic

/-!
# Duhamel operators on Fourier superpositions

Fubini identifies the literal cutoff primitive with the superposition
of its input modes. This links the proved DNY21 kernel to the operator.
-/

public section

open MeasureTheory Function
open scoped FourierTransform ContDiff RealInnerProductSpace SchwartzMap

namespace WaveTurbulence.Fourier

/-- The scalar truncated Duhamel operator, with its literal oriented interval integral. -/
@[expose] noncomputable def cutoffDuhamel (χ : ℝ → ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (χ t : ℂ) * ∫ u in (0 : ℝ)..t, (χ u : ℂ) * f u

/-- Input modes depend continuously on their frequency and time. -/
theorem duhamelPrimitive_joint_continuous {χ : ℝ → ℝ} (hχ : Continuous χ) :
    Continuous (fun p : ℝ × ℝ => duhamelPrimitive χ p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (s := fun p : ℝ × ℝ => p.2) (hs := continuous_snd)
  change Continuous (fun p : (ℝ × ℝ) × ℝ =>
    (χ p.2 : ℂ) * (Real.fourierChar (p.1.1 * p.2) : ℂ))
  fun_prop

/-- The cutoff input modes are jointly continuous. -/
theorem duhamelMode_joint_continuous {χ : ℝ → ℝ} (hχ : Continuous χ) :
    Continuous (fun p : ℝ × ℝ => duhamelMode χ p.1 p.2) :=
  (Complex.continuous_ofReal.comp (hχ.comp continuous_snd)).mul
    (duhamelPrimitive_joint_continuous hχ)

/-- The integrand for inserting a Fourier superposition is absolutely integrable. -/
theorem integrable_duhamel_superposition {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hi : Integrable χ) {h : ℝ → ℂ} (hh : Integrable h) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => (χ p.1 : ℂ) *
      (Real.fourierChar (p.2 * p.1) : ℂ) * h p.2)
      ((volume.restrict (Set.uIoc 0 t)).prod volume) := by
  have hm : Continuous (fun p : ℝ × ℝ => (χ p.1 : ℂ) *
      (Real.fourierChar (p.2 * p.1) : ℂ)) := by fun_prop
  apply ((hi.norm.restrict).mul_prod hh.norm).mono'
    (hm.aestronglyMeasurable.mul hh.aestronglyMeasurable.comp_snd)
  exact ae_of_all _ fun p => by
    simp [Complex.norm_real, Circle.norm_coe]

/-- The literal cutoff primitive commutes with an integrable Fourier superposition. -/
theorem cutoffDuhamel_superposition {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hi : Integrable χ) {h : ℝ → ℂ} (hh : Integrable h) (t : ℝ) :
    cutoffDuhamel χ (fun u => ∫ σ, (Real.fourierChar (σ * u) : ℂ) * h σ) t =
      ∫ σ, duhamelMode χ σ t * h σ := by
  unfold cutoffDuhamel
  simp_rw [← integral_const_mul]
  have hint : Integrable (uncurry (fun u σ : ℝ =>
      (χ u : ℂ) * ((Real.fourierChar (σ * u) : ℂ) * h σ)))
      ((volume.restrict (Set.uIoc 0 t)).prod volume) := by
    convert integrable_duhamel_superposition hχ hi hh t using 1
    funext p
    change (χ p.1 : ℂ) * ((Real.fourierChar (p.2 * p.1) : ℂ) * h p.2) = _
    ring
  rw [intervalIntegral_integral_swap hint]
  simp only [duhamelMode, duhamelPrimitive, mul_assoc]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun σ => by
    change (χ t : ℂ) * (∫ u in (0 : ℝ)..t,
      (χ u : ℂ) * ((Real.fourierChar (σ * u) : ℂ) * h σ)) =
      (χ t : ℂ) * ((∫ u in (0 : ℝ)..t,
        (χ u : ℂ) * (Real.fourierChar (σ * u) : ℂ)) * h σ)
    rw [← intervalIntegral.integral_mul_const]
    simp only [mul_assoc]

/-- The Fourier transform of an integrable superposition of Duhamel modes
is the integral against the DNY21 kernel. -/
theorem fourier_duhamel_superposition {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hi : Integrable χ) {h : ℝ → ℂ} (hh : Integrable h) (ξ : ℝ) :
    𝓕 (fun t => ∫ σ, duhamelMode χ σ t * h σ) ξ =
      ∫ σ, duhamelKernel χ ξ σ * h σ := by
  have hm : Continuous (fun p : ℝ × ℝ =>
      (Real.fourierChar (-⟪p.1, ξ⟫) : ℂ) * duhamelMode χ p.2 p.1) := by
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      (Real.fourierChar (-⟪p.1, ξ⟫) : ℂ))).mul
        ((duhamelMode_joint_continuous hχ).comp continuous_swap)
  have hint : Integrable (fun p : ℝ × ℝ =>
      (Real.fourierChar (-⟪p.1, ξ⟫) : ℂ) * (duhamelMode χ p.2 p.1 * h p.2)) := by
    have hh2 : AEStronglyMeasurable (fun p : ℝ × ℝ => h p.2) (volume.prod volume) :=
      hh.aestronglyMeasurable.comp_snd
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Real.fourierChar (-⟪p.1, ξ⟫) : ℂ) * (duhamelMode χ p.2 p.1 * h p.2))
        (volume.prod volume) := by
      convert hm.aestronglyMeasurable.mul hh2 using 1
      funext p
      change _ = ((Real.fourierChar (-⟪p.1, ξ⟫) : ℂ) * duhamelMode χ p.2 p.1) * h p.2
      ring
    apply (((hi.norm.mul_const (∫ u, |χ u|))).mul_prod hh.norm).mono' hmeas
    apply ae_of_all
    intro p
    simp only [norm_mul, Circle.norm_coe, one_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    change ‖(χ p.1 : ℂ) * duhamelPrimitive χ p.2 p.1‖ ≤ _
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_duhamelPrimitive_le hi _ _) (norm_nonneg _)
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, ← integral_const_mul]
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  exact ae_of_all _ fun σ => by
    simp only [duhamelKernel, Real.fourier_eq, Circle.smul_def, smul_eq_mul,
      ← integral_mul_const, mul_assoc]

/-- Fourier inversion identifies the kernel representation of the literal scalar operator. -/
theorem fourier_cutoffDuhamel_schwartz {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hi : Integrable χ) (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (cutoffDuhamel χ φ) ξ = ∫ σ, duhamelKernel χ ξ σ * 𝓕 (φ : ℝ → ℂ) σ := by
  have hh : Integrable (𝓕 (φ : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 φ).integrable
  have hinv := φ.continuous.fourierInv_fourier_eq φ.integrable hh
  have hrepr : (fun u : ℝ => ∫ σ, (Real.fourierChar (σ * u) : ℂ) *
      𝓕 (φ : ℝ → ℂ) σ) = φ := by
    funext u
    have h := congrFun hinv u
    simpa only [Real.fourierInv_eq, real_inner_comm, RCLike.inner_apply',
      conj_trivial, Circle.smul_def, smul_eq_mul] using h
  have hop : cutoffDuhamel χ φ = fun t => ∫ σ,
      duhamelMode χ σ t * 𝓕 (φ : ℝ → ℂ) σ := by
    funext t
    calc
      _ = cutoffDuhamel χ (fun u => ∫ σ, (Real.fourierChar (σ * u) : ℂ) *
          𝓕 (φ : ℝ → ℂ) σ) t := congrArg (fun f => cutoffDuhamel χ f t) hrepr.symm
      _ = _ := cutoffDuhamel_superposition hχ hi hh t
  rw [hop]
  exact fourier_duhamel_superposition hχ hi hh ξ

end WaveTurbulence.Fourier
