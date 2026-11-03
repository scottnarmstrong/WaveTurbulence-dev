/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Integrable inverse Japanese-bracket powers

The one-dimensional threshold is exponent greater than one. Products
in independent time coordinates are integrable by Fubini.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Fourier

/-- An inverse power of the scalar Japanese bracket. -/
@[expose] noncomputable def inverseBracketPower (q x : ℝ) : ℝ :=
  (Real.sqrt (1 + x ^ 2)) ^ (-q)

/-- Rewriting the bracket power in the form used by Mathlib's integrability theorem. -/
theorem inverseBracketPower_eq (q x : ℝ) :
    inverseBracketPower q x = (1 + x ^ 2) ^ (-q / 2) := by
  unfold inverseBracketPower
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ 1 + x ^ 2)]
  congr 1
  ring

/-- The sharp one-dimensional integrability range needed for the time estimates. -/
theorem integrable_inverseBracketPower {q : ℝ} (hq : 1 < q) :
    Integrable (inverseBracketPower q) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := q) (by simpa using hq)
  have he : inverseBracketPower q = (fun x : ℝ => (1 + x ^ 2) ^ (-q / 2)) :=
    funext (inverseBracketPower_eq q)
  rw [he]
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- Nonnegativity of inverse bracket powers. -/
theorem inverseBracketPower_nonneg (q x : ℝ) : 0 ≤ inverseBracketPower q x := by
  unfold inverseBracketPower
  positivity

/-- Products of integrable inverse bracket powers in two independent coordinates. -/
theorem integrable_inverseBracketPower_product {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    Integrable (fun z : ℝ × ℝ => inverseBracketPower p z.1 * inverseBracketPower q z.2) :=
  (integrable_inverseBracketPower hp).mul_prod (integrable_inverseBracketPower hq)

end WaveTurbulence.Fourier
