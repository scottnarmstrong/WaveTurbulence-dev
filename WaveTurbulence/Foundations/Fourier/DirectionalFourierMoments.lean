/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeDerivatives
public import WaveTurbulence.Foundations.Fourier.DuhamelKernelBound
import Mathlib.Tactic

/-!
# Fourier moments of ordered directional derivatives

Every derivative contributes its linear frequency. Dropping the harmless
factor `2π ≥ 1` bounds the resulting frequency moment by the derivative's
`L¹` norm. Smooth compact support supplies all integrability assumptions.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- A constant-direction time derivative. -/
@[expose] noncomputable def timeDirectionalDerivative {r : ℕ} (v : Fin r → ℝ)
    (f : (Fin r → ℝ) → ℂ) (x : Fin r → ℝ) : ℂ := fderiv ℝ f x v

/-- Directional derivatives preserve smoothness. -/
theorem timeDirectionalDerivative_contDiff {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (v : Fin r → ℝ) :
    ContDiff ℝ ∞ (timeDirectionalDerivative v f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact hd.clm_apply contDiff_const

/-- Directional derivatives preserve compact support. -/
theorem timeDirectionalDerivative_hasCompactSupport {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hc : HasCompactSupport f) (v : Fin r → ℝ) :
    HasCompactSupport (timeDirectionalDerivative v f) := hc.fderiv_apply ℝ v

/-- A list of constant-direction derivatives, applied from right to left. -/
@[expose] noncomputable def timeWordDerivative {r : ℕ} :
    List (Fin r → ℝ) → ((Fin r → ℝ) → ℂ) → ((Fin r → ℝ) → ℂ)
  | [], f => f
  | v :: w, f => timeDirectionalDerivative v (timeWordDerivative w f)

/-- Word derivatives of a smooth compact function remain smooth and compact. -/
theorem timeWordDerivative_regular {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (w : List (Fin r → ℝ)) :
    ContDiff ℝ ∞ (timeWordDerivative w f) ∧ HasCompactSupport (timeWordDerivative w f) := by
  induction w with
  | nil => exact ⟨hf, hc⟩
  | cons v w ih => exact ⟨timeDirectionalDerivative_contDiff ih.1 v,
      timeDirectionalDerivative_hasCompactSupport ih.2 v⟩

/-- Fourier multiplication for one directional derivative, with integrability supplied internally. -/
theorem timeFourier_directional_smooth_compact {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (v ξ : Fin r → ℝ) :
    timeFourier (timeDirectionalDerivative v f) ξ =
      (2 * Real.pi * Complex.I * (timePairing r v ξ : ℂ)) * timeFourier f ξ :=
  timeFourier_fderiv_apply (hf.continuous.integrable_of_hasCompactSupport hc)
    (hf.differentiable (by simp))
    ((hf.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hc.fderiv ℝ)) v ξ

/-- Square-free or repeated directional moments are bounded by the corresponding Fourier transform. -/
theorem timeFourier_word_moment_le {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (w : List (Fin r → ℝ)) (ξ : Fin r → ℝ) :
    (w.map (fun v => |timePairing r v ξ|)).prod * ‖timeFourier f ξ‖ ≤
      ‖timeFourier (timeWordDerivative w f) ξ‖ := by
  induction w with
  | nil => simp [timeWordDerivative]
  | cons v w ih =>
    obtain ⟨hw, hcw⟩ := timeWordDerivative_regular hf hc w
    simp only [List.map_cons, List.prod_cons]
    calc
      _ = |timePairing r v ξ| *
          ((w.map (fun v => |timePairing r v ξ|)).prod * ‖timeFourier f ξ‖) := by ring
      _ ≤ |timePairing r v ξ| * ‖timeFourier (timeWordDerivative w f) ξ‖ :=
        mul_le_mul_of_nonneg_left ih (abs_nonneg _)
      _ ≤ ‖(2 * Real.pi * Complex.I * (timePairing r v ξ : ℂ)) *
          timeFourier (timeWordDerivative w f) ξ‖ := abs_mul_norm_le_fourier_multiplier _ _
      _ = _ := by rw [← timeFourier_directional_smooth_compact hw hcw]; rfl

/-- The `L¹` form of the directional Fourier-moment estimate. -/
theorem timeFourier_word_moment_le_integral {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (w : List (Fin r → ℝ)) (ξ : Fin r → ℝ) :
    (w.map (fun v => |timePairing r v ξ|)).prod * ‖timeFourier f ξ‖ ≤
      ∫ x, ‖timeWordDerivative w f x‖ :=
  (timeFourier_word_moment_le hf hc w ξ).trans
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _)

/-- Coordinate directional derivatives agree with the frozen partial derivative. -/
theorem timeDirectionalDerivative_single {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Differentiable ℝ f) (j : Fin r) :
    timeDirectionalDerivative (Pi.single j 1) f = WaveTurbulence.partialDeriv j f :=
  (WaveTurbulence.partialDeriv_eq_fderiv_fun hf j).symm

/-- The diagonal derivative is the sum of the two frozen time partials. -/
theorem timeDirectionalDerivative_diagonal_eq_partials {f : (Fin 2 → ℝ) → ℂ}
    (hf : Differentiable ℝ f) (t : Fin 2 → ℝ) :
    timeDirectionalDerivative (fun _ => 1) f t =
      WaveTurbulence.partialDeriv 0 f t + WaveTurbulence.partialDeriv 1 f t := by
  rw [WaveTurbulence.partialDeriv_eq_fderiv_fun hf 0,
    WaveTurbulence.partialDeriv_eq_fderiv_fun hf 1]
  have hv : (fun _ : Fin 2 => (1 : ℝ)) = Pi.single 0 1 + Pi.single 1 1 := by
    ext j
    fin_cases j <;> simp
  change fderiv ℝ f t (fun _ => 1) = fderiv ℝ f t (Pi.single 0 1) + fderiv ℝ f t (Pi.single 1 1)
  rw [hv, map_add]

/-- Simultaneous translation has the all-ones tangent vector. -/
theorem hasDerivAt_time_translation {r : ℕ} (v : Fin r → ℝ) (c : ℝ) :
    HasDerivAt (fun u : ℝ => fun j : Fin r => v j + u) (fun _ => 1) c := by
  apply hasDerivAt_pi.mpr
  intro j
  exact (hasDerivAt_id c).const_add (v j)

/-- The diagonal directional derivative is the derivative of simultaneous translation. -/
theorem hasDerivAt_diagonal_translation {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Differentiable ℝ f) (v : Fin r → ℝ) :
    HasDerivAt (fun c : ℝ => f (fun j => v j + c))
      (timeDirectionalDerivative (fun _ => 1) f v) 0 := by
  have h := (hf (fun j => v j + (0 : ℝ))).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_time_translation v 0)
  simpa only [Function.comp_def, add_zero, timeDirectionalDerivative] using h

end WaveTurbulence.Fourier
