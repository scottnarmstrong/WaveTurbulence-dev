/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BoxIntegralAlgebra
import Mathlib.Tactic

/-!
# The two distinguished source coordinates in the A.3 box integrals

The fourfold operator uses the middle two integration coordinates.
The two unused outer coordinates contribute exactly two interval widths.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Selecting both coordinates in dimension two changes no box integral. -/
theorem boxIntegral_two_coordinate_pair (f : (Fin 2 → ℝ) → ℝ≥0∞) (R : ℝ) :
    boxIntegral 2 (fun v => f ![v 0, v 1]) R = boxIntegral 2 f R := by
  apply congrArg (fun g => boxIntegral 2 g R)
  funext v
  congr 1
  ext j
  fin_cases j <;> rfl

/-- Selecting the middle coordinates in dimension four costs the two unused widths. -/
theorem boxIntegral_four_middle (f : (Fin 2 → ℝ) → ℝ≥0∞) (R : ℝ) :
    boxIntegral 4 (fun v => f ![v 1, v 2]) R =
      volume (Icc (-R) R) ^ 2 * boxIntegral 2 f R := by
  have hw : volume (Icc (-R) R) ≠ ⊤ := isCompact_Icc.measure_lt_top.ne
  rw [boxIntegral_two]
  change (∫⁻ _u in Icc (-R) R, ∫⁻ a in Icc (-R) R, ∫⁻ b in Icc (-R) R,
    ∫⁻ _v in Icc (-R) R, f ![a, b]) =
      volume (Icc (-R) R) ^ 2 * ∫⁻ a in Icc (-R) R, ∫⁻ b in Icc (-R) R, f ![a, b]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  have he (a : ℝ) : (∫⁻ b in Icc (-R) R, f ![a, b] * volume (Icc (-R) R)) =
      (∫⁻ b in Icc (-R) R, f ![a, b]) * volume (Icc (-R) R) :=
    lintegral_mul_const' _ _ hw
  simp_rw [he]
  rw [lintegral_mul_const' (volume (Icc (-R) R))
    (fun a : ℝ => ∫⁻ b in Icc (-R) R, f ![a, b]) hw]
  ring

end WaveTurbulence.Fourier
