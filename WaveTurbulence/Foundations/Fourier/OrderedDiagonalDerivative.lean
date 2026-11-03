/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedParameterDerivative
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-!
# Simultaneous translation derivatives of ordered integrals

Translating both endpoints translates every integration variable.
The derivative therefore acts on the amplitude in the all-ones direction.
Difference phases have zero derivative in that direction.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Simultaneous endpoint translation differentiates the amplitude in the diagonal direction. -/
theorem hasDerivAt_orderedIntegral_diagonal {n : ℕ} {F : (Fin n → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (t s : ℝ) :
    HasDerivAt (fun c => orderedIntegral n F (t + c) (s + c))
      (orderedIntegral n (fun v => fderiv ℝ F v (fun _ => 1)) t s) 0 := by
  let G : ℝ × (Fin n → ℝ) → ℂ := fun p => F (fun i => p.2 i + p.1)
  have hG : ContDiff ℝ ∞ G := by
    apply hF.comp
    apply contDiff_pi.mpr
    intro i
    fun_prop
  have heval : (fun v => fderiv ℝ G (0, v) (1, 0)) =
      (fun v => fderiv ℝ F v (fun _ => 1)) := by
    funext v
    have hc : HasDerivAt (fun c : ℝ => fun i : Fin n => v i + c) (fun _ => 1) 0 := by
      apply hasDerivAt_pi.mpr
      intro i
      exact (hasDerivAt_id (0 : ℝ)).const_add (v i)
    have hcurve := (hF.differentiable (by simp) (fun i => v i + (0 : ℝ))).hasFDerivAt.comp_hasDerivAt 0 hc
    have hslice := hasDerivAt_parameter_slice hG 0 v
    simpa only [add_zero] using hslice.unique hcurve
  have h := hasDerivAt_orderedIntegral_parameter n hG 0 t s
  rw [heval] at h
  convert h using 1
  funext c
  exact orderedIntegral_translate n F t s c

/-- Directional derivative of the two-time ordered output in the all-ones direction. -/
theorem fderiv_orderedIntegral_diagonal {n : ℕ} {F : (Fin n → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (t : Fin 2 → ℝ) :
    fderiv ℝ (fun z : Fin 2 → ℝ => orderedIntegral n F (z 0) (z 1)) t (fun _ => 1) =
      orderedIntegral n (fun v => fderiv ℝ F v (fun _ => 1)) (t 0) (t 1) := by
  have hs : ContDiff ℝ ∞ (fun z : Fin 2 → ℝ => orderedIntegral n F (z 0) (z 1)) :=
    contDiff_orderedIntegral n (hF.comp contDiff_snd) (by fun_prop) (by fun_prop)
  have hc : HasDerivAt (fun c : ℝ => fun i : Fin 2 => t i + c) (fun _ => 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    exact (hasDerivAt_id (0 : ℝ)).const_add (t i)
  have h := (hs.differentiable (by simp) (fun i => t i + (0 : ℝ))).hasFDerivAt.comp_hasDerivAt 0 hc
  simpa only [add_zero] using h.unique (hasDerivAt_orderedIntegral_diagonal hF (t 0) (t 1))

end WaveTurbulence.Fourier
