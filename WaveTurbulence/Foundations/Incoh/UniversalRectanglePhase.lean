/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RectanglePhaseBound
public import WaveTurbulence.Foundations.Incoh.MixedParameterPullback

/-!
# A universal family of rectangular phase kernels

The six real parameters comprise two phases and four interval endpoints.
A single mixed Fourier envelope therefore controls all such kernels, even
when their parameters also depend on the remaining internal clocks.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Lower endpoints encoded by the universal six-dimensional parameter. -/
@[expose] def rectanglePhaseLower (p : Mom 6) : Fin 2 → ℝ :=
  ![min (p 2) (p 4), min (p 3) (p 5)]

/-- Upper endpoints encoded by the same parameter. -/
@[expose] def rectanglePhaseUpper (p : Mom 6) : Fin 2 → ℝ :=
  ![max (p 2) (p 4), max (p 3) (p 5)]

theorem rectanglePhaseLower_le_upper (p : Mom 6) : rectanglePhaseLower p ≤ rectanglePhaseUpper p := by
  intro j
  fin_cases j <;> exact min_le_max

/-- The universal triangular kernel family. -/
@[expose] def universalRectangleU (χ : ℝ → ℝ) : (Fin 2 → ℝ) → Mom 6 → ℂ :=
  Fourier.cutoffU χ (fun p => p 0)
    (fun t p => rectangleIndicator (rectanglePhaseLower p) (rectanglePhaseUpper p) t)

/-- The universal fourfold kernel family. -/
@[expose] def universalRectangleV (χ : ℝ → ℝ) : (Fin 2 → ℝ) → Mom 6 → ℂ :=
  Fourier.cutoffV χ (fun p => p 0) (fun p => p 1)
    (fun t p => rectangleIndicator (rectanglePhaseLower p) (rectanglePhaseUpper p) t)

/-- Encoding any ordered pair of intervals and any two real phases. -/
@[expose] def rectanglePhaseCode (Γ₁ Γ₂ : ℝ) (a b : Fin 2 → ℝ) : Mom 6 :=
  WithLp.toLp 2 ![Γ₁, Γ₂, a 0, a 1, b 0, b 1]

theorem rectanglePhaseLower_code (Γ₁ Γ₂ : ℝ) (a b : Fin 2 → ℝ) (hab : a ≤ b) :
    rectanglePhaseLower (rectanglePhaseCode Γ₁ Γ₂ a b) = a := by
  ext j
  fin_cases j
  · change min (a 0) (b 0) = a 0
    exact min_eq_left (hab 0)
  · change min (a 1) (b 1) = a 1
    exact min_eq_left (hab 1)

theorem rectanglePhaseUpper_code (Γ₁ Γ₂ : ℝ) (a b : Fin 2 → ℝ) (hab : a ≤ b) :
    rectanglePhaseUpper (rectanglePhaseCode Γ₁ Γ₂ a b) = b := by
  ext j
  fin_cases j
  · change max (a 0) (b 0) = b 0
    exact max_eq_right (hab 0)
  · change max (a 1) (b 1) = b 1
    exact max_eq_right (hab 1)

/-- A common integrable Fourier envelope controls every interval and phase choice. -/
theorem exists_universalRectangle_phase_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧
    Fourier.mixedFourierNorm00 (1 / 4) (universalRectangleU χ) ≤ ENNReal.ofReal C ∧
    Fourier.mixedFourierNorm00 (1 / 4) (universalRectangleV χ) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := exists_rectangle_phase_bound hχ hcχ
  refine ⟨C, hC, ?_⟩
  simpa only [universalRectangleU, universalRectangleV, Fourier.mixedFourierNorm00_eq_mixedFourierNorm]
    using hb 6 (fun p => p 0) (fun p => p 1) rectanglePhaseLower rectanglePhaseUpper
      rectanglePhaseLower_le_upper

/-- Arbitrary additional parameter dependence preserves the universal triangular bound. -/
theorem universalRectangleU_pullback_bound {χ : ℝ → ℝ} {C : ℝ≥0∞}
    (h : Fourier.mixedFourierNorm00 (1 / 4) (universalRectangleU χ) ≤ C)
    {V : Type*} (p : V → Mom 6) :
    Fourier.mixedFourierNorm00 (1 / 4) (fun t v => universalRectangleU χ t (p v)) ≤ C :=
  (mixedFourierNorm00_comp_le (1 / 4) (universalRectangleU χ) p).trans h

/-- The corresponding arbitrary-parameter fourfold bound. -/
theorem universalRectangleV_pullback_bound {χ : ℝ → ℝ} {C : ℝ≥0∞}
    (h : Fourier.mixedFourierNorm00 (1 / 4) (universalRectangleV χ) ≤ C)
    {V : Type*} (p : V → Mom 6) :
    Fourier.mixedFourierNorm00 (1 / 4) (fun t v => universalRectangleV χ t (p v)) ≤ C :=
  (mixedFourierNorm00_comp_le (1 / 4) (universalRectangleV χ) p).trans h

end WaveTurbulence.Incoh
