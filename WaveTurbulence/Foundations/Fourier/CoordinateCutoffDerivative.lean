/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CoordinateCutoff
public import WaveTurbulence.Foundations.Fourier.CutoffControl
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Simultaneous-translation derivative of a product cutoff

The finite product rule gives a frequency-independent derivative bound.
Only the scalar cutoff and its first derivative enter this amplitude bound.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Uniform pointwise bound for a product of cutoff factors. -/
theorem norm_coordinateCutoff_le {n : ℕ} {χ : ℝ → ℝ} (h : CutoffControl χ) (v : Fin n → ℝ) :
    ‖coordinateCutoff χ v‖ ≤ h.bound ^ n := by
  unfold coordinateCutoff
  rw [norm_prod]
  calc
    _ ≤ ∏ _j : Fin n, h.bound := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      simpa only [Complex.norm_real, Real.norm_eq_abs] using h.abs_le (v j)
    _ = _ := by simp

end WaveTurbulence.Fourier
