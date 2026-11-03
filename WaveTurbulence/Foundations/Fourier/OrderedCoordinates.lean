/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedIntegral
import Mathlib.Tactic

/-!
# Coordinate formulas for ordered time integrals

These identities identify the recursive simplex integrals with the exact
twofold and fourfold formulas in TARGET A.2–A.3.
-/

public section

namespace WaveTurbulence.Fourier

/-- The twofold ordered integral, in the paper's coordinates. -/
theorem orderedIntegral_two (F : (Fin 2 → ℝ) → ℂ) (t s : ℝ) :
    orderedIntegral 2 F t s = ∫ u in s..t, ∫ v in s..u, F ![u, v] := by
  simp only [orderedIntegral]
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro v _
  congr 1

/-- The fourfold ordered integral, in the paper's coordinates. -/
theorem orderedIntegral_four (F : (Fin 4 → ℝ) → ℂ) (t s : ℝ) :
    orderedIntegral 4 F t s =
      ∫ u in s..t, ∫ a in s..u, ∫ b in s..a, ∫ v in s..b, F ![u, a, b, v] := by
  simp only [orderedIntegral]
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro a _
  apply intervalIntegral.integral_congr
  intro b _
  apply intervalIntegral.integral_congr
  intro v _
  congr 1

end WaveTurbulence.Fourier
