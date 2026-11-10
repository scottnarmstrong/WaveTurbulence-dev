/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CutoffOrderedIntegral
public import WaveTurbulence.Foundations.Fourier.TimeIntegralOperators
import Mathlib.Tactic

/-!
# Regularity of the literal time-integral operators

The smoothness assumptions concern time slices only. In particular the
momentum phases in TARGET A.3 are arbitrary functions, as in the source
and the owner's order-zero mixed-norm ruling.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The amplitude of the triangular time integral. -/
@[expose] def triangleAmplitude (χ : ℝ → ℝ) (F : (Fin 2 → ℝ) → ℂ) (v : Fin 2 → ℝ) : ℂ :=
  coordinateCutoff χ v * F v

/-- Literal identification of the triangular operator with ordered integration. -/
theorem cutoffTriangleIntegral_eq_ordered (χ : ℝ → ℝ) (F : (Fin 2 → ℝ) → ℂ) :
    cutoffTriangleIntegral χ F = cutoffOrderedIntegral 2 χ (triangleAmplitude χ F) := by
  funext t
  simp [cutoffTriangleIntegral, cutoffOrderedIntegral, triangleAmplitude,
    coordinateCutoff, orderedIntegral_two, Fin.prod_univ_two]

/-- Smooth real phases exponentiate smoothly in the paper's `exp(iφ)` convention. -/
theorem contDiff_exp_real_phase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun v => Complex.exp ((φ v : ℂ) * Complex.I)) :=
  ((Complex.ofRealCLM.contDiff.comp hφ).mul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : E => Complex.I))).cexp

/-- Smoothness of the triangular amplitude. -/
theorem triangleAmplitude_contDiff {χ : ℝ → ℝ} {F : (Fin 2 → ℝ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (triangleAmplitude χ F) :=
  (coordinateCutoff_contDiff hχ).mul hF

/-- Smoothness of the literal triangular operator. -/
theorem cutoffTriangleIntegral_contDiff {χ : ℝ → ℝ} {F : (Fin 2 → ℝ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (cutoffTriangleIntegral χ F) := by
  rw [cutoffTriangleIntegral_eq_ordered]
  exact cutoffOrderedIntegral_contDiff hχ (triangleAmplitude_contDiff hχ hF)

/-- Compact support of the triangular output follows from the output cutoffs. -/
theorem cutoffTriangleIntegral_hasCompactSupport {χ : ℝ → ℝ}
    (hc : HasCompactSupport χ) (F : (Fin 2 → ℝ) → ℂ) :
    HasCompactSupport (cutoffTriangleIntegral χ F) := by
  rw [cutoffTriangleIntegral_eq_ordered]
  exact cutoffOrderedIntegral_hasCompactSupport hc _

end WaveTurbulence.Fourier
