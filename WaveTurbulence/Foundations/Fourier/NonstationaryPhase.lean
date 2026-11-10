/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic

/-!
# Uniform non-stationary phase for translated smooth cutoffs

TARGET L966, L1550. Translation only changes the Fourier transform by a
unit complex phase. Schwartz seminorms of the fixed amplitude's Fourier
transform give rapid decay uniformly in the translation parameter.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Translation of an amplitude preserves the absolute Fourier integral. -/
theorem norm_oscillatory_translate_eq (f : V → ℂ) (a w : V) :
    ‖∫ x, Real.fourierChar (inner ℝ x w) • f (x - a)‖ = ‖𝓕 f (-w)‖ := by
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ V) f (-a)) (-w)
  have hn := congrArg norm ht
  simpa only [VectorFourier.fourierIntegral, Function.comp_apply, innerₗ_apply_apply, inner_neg_right,
    neg_neg, ← sub_eq_add_neg, Circle.norm_smul, Real.fourier_eq] using hn

end WaveTurbulence.Fourier
