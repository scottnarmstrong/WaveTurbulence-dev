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

/-- The amplitude of the fourfold ordered time integral. -/
@[expose] noncomputable def fourfoldAmplitude (χ : ℝ → ℝ) (Γ₁ Γ₂ : ℝ)
    (F : (Fin 2 → ℝ) → ℂ) (v : Fin 4 → ℝ) : ℂ :=
  coordinateCutoff χ v * Complex.exp ((Γ₁ * (v 0 - v 1) : ℝ) * Complex.I) *
    Complex.exp ((Γ₂ * (v 2 - v 3) : ℝ) * Complex.I) * F ![v 1, v 2]

/-- Literal identification of the triangular operator with ordered integration. -/
theorem cutoffTriangleIntegral_eq_ordered (χ : ℝ → ℝ) (F : (Fin 2 → ℝ) → ℂ) :
    cutoffTriangleIntegral χ F = cutoffOrderedIntegral 2 χ (triangleAmplitude χ F) := by
  funext t
  simp [cutoffTriangleIntegral, cutoffOrderedIntegral, triangleAmplitude,
    coordinateCutoff, orderedIntegral_two, Fin.prod_univ_two]

/-- Literal identification of the fourfold source operator with ordered integration. -/
theorem cutoffV_eq_ordered {d : ℕ} (χ : ℝ → ℝ) (Γ₁ Γ₂ : Mom d → ℝ)
    (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d) :
    (fun t => cutoffV χ Γ₁ Γ₂ F t k) =
      cutoffOrderedIntegral 4 χ (fourfoldAmplitude χ (Γ₁ k) (Γ₂ k) (fun u => F u k)) := by
  funext t
  simp [cutoffV, cutoffOrderedIntegral, orderedIntegral_four, fourfoldAmplitude,
    coordinateCutoff, Fin.prod_univ_succ, mul_assoc]

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

/-- Smoothness of the fourfold amplitude, uniformly as a statement in the phase parameters. -/
theorem fourfoldAmplitude_contDiff {χ : ℝ → ℝ} {F : (Fin 2 → ℝ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (Γ₁ Γ₂ : ℝ) :
    ContDiff ℝ ∞ (fourfoldAmplitude χ Γ₁ Γ₂ F) := by
  apply (((coordinateCutoff_contDiff hχ).mul (contDiff_exp_real_phase (by fun_prop))).mul
    (contDiff_exp_real_phase (by fun_prop))).mul
  apply hF.comp
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => v 1)
    fun_prop
  · change ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => v 2)
    fun_prop

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

/-- Every smooth time slice of `𝒰χ` is integrable, even for arbitrary momentum phases. -/
theorem cutoffU_integrable {d : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (Γ : Mom d → ℝ)
    {F : (Fin 2 → ℝ) → Mom d → ℂ} (hF : ∀ k, ContDiff ℝ ∞ (fun t => F t k))
    (k : Mom d) : Integrable (fun t => cutoffU χ Γ F t k) := by
  have hs : ContDiff ℝ ∞ (fun t => Complex.exp ((Γ k * (t 0 - t 1) : ℝ) * Complex.I) * F t k) :=
    (contDiff_exp_real_phase (by fun_prop)).mul (hF k)
  exact (cutoffTriangleIntegral_contDiff hχ hs).continuous.integrable_of_hasCompactSupport
    (cutoffTriangleIntegral_hasCompactSupport hc _)

/-- Every smooth time slice of `𝒱χ` is integrable, even for arbitrary momentum phases. -/
theorem cutoffV_integrable {d : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (Γ₁ Γ₂ : Mom d → ℝ)
    {F : (Fin 2 → ℝ) → Mom d → ℂ} (hF : ∀ k, ContDiff ℝ ∞ (fun t => F t k))
    (k : Mom d) : Integrable (fun t => cutoffV χ Γ₁ Γ₂ F t k) := by
  rw [cutoffV_eq_ordered]
  exact cutoffOrderedIntegral_integrable hχ hc (fourfoldAmplitude_contDiff hχ (hF k) _ _)

end WaveTurbulence.Fourier
