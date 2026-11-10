/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Joint frequency decay from finitely many Fourier moments

Controlling all square-free products of a finite collection of frequencies
gives a product of inverse Japanese brackets. This is the elementary
algebra used after integration by parts in DNY21 Lemma 3.1 and TARGET A.3.
-/

public section

namespace WaveTurbulence.Fourier

/-- The Japanese bracket is bounded by one plus absolute value. -/
theorem japaneseBracket_le_one_add_abs (x : ℝ) :
    Real.sqrt (1 + x ^ 2) ≤ 1 + |x| := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (1 + x ^ 2)
  nlinarith [sq_abs x, abs_nonneg x]

/-- Two-frequency specialization, with separate moment hypotheses for convenient use. -/
theorem frequency_decay_two (z : ℂ) (x y C : ℝ)
    (h0 : ‖z‖ ≤ C) (hx : |x| * ‖z‖ ≤ C) (hy : |y| * ‖z‖ ≤ C)
    (hxy : (|x| * |y|) * ‖z‖ ≤ C) :
    ‖z‖ ≤ 4 * C / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) := by
  have hp : 0 < Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) := by positivity
  apply (le_div_iff₀ hp).mpr
  have hb := mul_le_mul (japaneseBracket_le_one_add_abs x)
    (japaneseBracket_le_one_add_abs y) (Real.sqrt_nonneg _) (by positivity : 0 ≤ 1 + |x|)
  have hz := mul_le_mul_of_nonneg_left hb (norm_nonneg z)
  nlinarith

/-- Three-frequency specialization for the eight square-free directional moments. -/
theorem frequency_decay_three (z : ℂ) (x y w C : ℝ)
    (h0 : ‖z‖ ≤ C) (hx : |x| * ‖z‖ ≤ C) (hy : |y| * ‖z‖ ≤ C)
    (hw : |w| * ‖z‖ ≤ C) (hxy : (|x| * |y|) * ‖z‖ ≤ C)
    (hxw : (|x| * |w|) * ‖z‖ ≤ C) (hyw : (|y| * |w|) * ‖z‖ ≤ C)
    (hxyw : (|x| * |y| * |w|) * ‖z‖ ≤ C) :
    ‖z‖ ≤ 8 * C /
      (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) * Real.sqrt (1 + w ^ 2)) := by
  have hp : 0 < Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) *
      Real.sqrt (1 + w ^ 2) := by positivity
  apply (le_div_iff₀ hp).mpr
  have hxyb := mul_le_mul (japaneseBracket_le_one_add_abs x)
    (japaneseBracket_le_one_add_abs y) (Real.sqrt_nonneg _) (by positivity : 0 ≤ 1 + |x|)
  have hprod := mul_le_mul hxyb (japaneseBracket_le_one_add_abs w)
    (Real.sqrt_nonneg _) (by positivity : 0 ≤ (1 + |x|) * (1 + |y|))
  calc
    _ ≤ ‖z‖ * ((1 + |x|) * (1 + |y|) * (1 + |w|)) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖z‖ + |x| * ‖z‖ + |y| * ‖z‖ + |w| * ‖z‖ +
        (|x| * |y|) * ‖z‖ + (|x| * |w|) * ‖z‖ + (|y| * |w|) * ‖z‖ +
        (|x| * |y| * |w|) * ‖z‖ := by ring
    _ ≤ _ := by linarith

end WaveTurbulence.Fourier
