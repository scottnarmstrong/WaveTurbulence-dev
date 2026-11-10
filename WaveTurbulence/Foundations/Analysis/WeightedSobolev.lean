/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CubeSobolev
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Weighted whole-space Sobolev estimates

A product integrable envelope for the mixed derivatives gives an explicit
pointwise bound. The standard envelope is `∏ i, (1 + x_i²)⁻¹`.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The mixed partial derivative selected by a Boolean vector. Each
coordinate is differentiated at most once, in increasing coordinate order. -/
@[expose] noncomputable def mixedPartial : (n : ℕ) → (Fin n → Bool) →
    ((Fin n → ℝ) → E) → (Fin n → ℝ) → E
  | 0, _, f, x => f x
  | n + 1, b, f, x =>
      if b 0 then
        mixedPartial n (Fin.tail b)
          (fun y => deriv (fun s => f (Fin.cons s y)) (x 0)) (Fin.tail x)
      else mixedPartial n (Fin.tail b) (fun y => f (Fin.cons (x 0) y)) (Fin.tail x)

end WaveTurbulence.Analysis
