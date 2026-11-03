/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Explicit source scales and B-process error for the circle family

These are concrete numeric functions, not analytic hypotheses. The
curvature and cubic scales come from the proved actual derivative bounds.
-/

public section

namespace WaveTurbulence.VdCB

@[expose] noncomputable def circleCurvatureLower (R h U : ℝ) : ℝ :=
  h * R ^ 2 * (4 * R * U) ^ (-(3 / 2) : ℝ)

@[expose] noncomputable def circleCurvatureUpper (R h U : ℝ) : ℝ :=
  h * R ^ 2 * (R * U) ^ (-(3 / 2) : ℝ)

@[expose] noncomputable def circleThirdScale (R h U : ℝ) : ℝ :=
  3 * h * R ^ 3 * (R * U) ^ (-(5 / 2) : ℝ)

/-- The source scale for the transformed pair `(11/30,16/30)`. -/
@[expose] noncomputable def circleBScale (R h U : ℝ) : ℝ :=
  h ^ ((11 : ℝ) / 30) * R ^ ((11 : ℝ) / 60) * U ^ ((7 : ℝ) / 20)

/-- Explicit unoptimized Poisson, omitted-frequency and stationary errors. -/
@[expose] noncomputable def circleBError (R h U r t : ℝ) : ℝ :=
  ((2 + 6 * Real.log (circleCurvatureUpper R h U * U + 3)) / (2 * Real.pi) + 1) +
  2 * (circleCurvatureUpper R h U * r + 3) *
    (2 * t / circleCurvatureLower R h U + 2 / (Real.pi * t)) +
  (circleCurvatureUpper R h U * U + 3) *
    (2 * Real.pi / 3 * circleThirdScale R h U * r ^ 4 + 4 / (Real.pi * (circleCurvatureLower R h U * r)))

end WaveTurbulence.VdCB
