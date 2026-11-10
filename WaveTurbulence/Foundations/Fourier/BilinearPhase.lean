/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.NonstationaryPhase
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Bilinear stationary phase by a Fourier change of variables

TARGET L968; DH23 L1013ff. Integrating one variable produces the Fourier
transform of its amplitude at `-(ξ+s y)`. Its `L¹` norm after dilation is
`|s|^{-d}` times the original Fourier-L¹ norm, uniformly in all translations
and linear frequencies. No general stationary-phase theorem is used.
-/

public section

open MeasureTheory Module
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The bilinear oscillatory integral, with the paper's `2π` phase. -/
@[expose] noncomputable def bilinearPhaseIntegral (f g : V → ℂ)
    (a b ξ ζ : V) (s : ℝ) : ℂ :=
  ∫ y, ∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) •
    (f (x - a) * g (y - b))

/-- A fixed-amplitude constant for the bilinear stationary-phase estimate. -/
@[expose] noncomputable def bilinearPhaseConstant (f g : 𝓢(V, ℂ)) : ℝ :=
  (2 : ℝ) ^ (finrank ℝ V - 1) *
    ((∫ x, ‖f x‖) * (∫ y, ‖g y‖) +
      SchwartzMap.seminorm ℂ 0 0 g * ∫ η, ‖𝓕 f η‖)

end WaveTurbulence.Fourier
