/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeInterpolation
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Fourier factorization for independent vector blocks

TARGET L1007–L1012: products in independent momentum variables have
factorized Fourier transforms and Fourier-L¹ norms.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Fourier transform in `n` blocks of `d` scalar coordinates. -/
@[expose] noncomputable def blockFourier {n d : ℕ}
    (F : (Fin n → Fin d → ℝ) → ℂ) (ξ : Fin n → Fin d → ℝ) : ℂ :=
  ∫ x, Real.fourierChar (-(∑ i, timePairing d (x i) (ξ i))) • F x

end WaveTurbulence.Fourier
