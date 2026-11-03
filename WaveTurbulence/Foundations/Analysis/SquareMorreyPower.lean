/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.SquareMorrey

/-!
# Powered Morrey estimate and the large parameter

TARGET (sobolev2), L2330, with explicit constants and exponent range.
The real exponent `p` in this file corresponds to `2P` in the paper.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Powered square Morrey estimate. The two coefficients depend only on
the exponents; neither depends on the function or the radius. -/
theorem enorm_rpow_le_square_morrey {f : Mom 2 → F} (hf : ContDiff ℝ 1 f)
    {x : Mom 2} (hx : x ∈ closedSquare 0 1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ‖f x‖ₑ ^ p ≤ (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (r ^ (-2 : ℝ)) *
      (∫⁻ y in closedSquare 0 1, ‖f y‖ₑ ^ p) +
        (2 * squareMorreyConstant q) ^ p * ENNReal.ofReal (r ^ (p - 2)) *
          (∫⁻ z in closedSquare 0 1, ‖fderiv ℝ f z‖ₑ ^ p) := by
  have hh := ENNReal.rpow_le_rpow (enorm_le_square_morrey_normalized hf hx hr hr1 hpq) hpq.nonneg
  have ha := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
    (ENNReal.ofReal (r ^ (-2 / p)) *
      (∫⁻ y in closedSquare 0 1, ‖f y‖ₑ ^ p) ^ (1 / p))
    (squareMorreyConstant q * ENNReal.ofReal (r ^ (1 - 2 / p)) *
      (∫⁻ z in closedSquare 0 1, ‖fderiv ℝ f z‖ₑ ^ p) ^ (1 / p)) hpq.nonneg
  rw [morrey_power_first hr hpq.pos, morrey_power_second hr hpq.pos] at ha
  refine (hh.trans ha).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg]
  ring

/-- The elementary exponent comparison behind the two losses in (sobolev2).
It is isolated from all real-power expressions. -/
theorem morrey_gradient_exponent_le {p : ℝ} (hp : 20002 ≤ p) :
    (-p / 400) * (p - 2) ≤ -50 * p := by
  have hh := mul_nonneg (show 0 ≤ p by linarith only [hp]) (sub_nonneg.mpr hp)
  nlinarith only [hh]

/-- TARGET (sobolev2), L2330, in extended-integral form. For `p = 2P`,
the sufficient range is `P ≥ 10001`. The explicit coefficients replace
the paper's implicit multiplicative constants. The first derivative is the
Fréchet derivative in the two time variables. -/
theorem enorm_rpow_le_square_morrey_largeParameter {f : Mom 2 → F}
    (hf : ContDiff ℝ 1 f) {x : Mom 2} (hx : x ∈ closedSquare 0 1)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp : 20002 ≤ p)
    {M : ℝ} (hM : 1 ≤ M) :
    ‖f x‖ₑ ^ p ≤ (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (M ^ (p / 200)) *
      (∫⁻ y in closedSquare 0 1, ‖f y‖ₑ ^ p) +
        (2 * squareMorreyConstant q) ^ p * ENNReal.ofReal (M ^ (-50 * p)) *
          (∫⁻ z in closedSquare 0 1, ‖fderiv ℝ f z‖ₑ ^ p) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let r := M ^ (-p / 400)
  have hr : 0 < r := Real.rpow_pos_of_pos hM0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith only [hp])
  have hh := enorm_rpow_le_square_morrey hf hx hr hr1 hpq
  have he : r ^ (-2 : ℝ) = M ^ (p / 200) := by
    dsimp only [r]
    rw [← Real.rpow_mul hM0.le]
    congr 1
    ring
  rw [he] at hh
  have hd : r ^ (p - 2) ≤ M ^ (-50 * p) := by
    dsimp only [r]
    rw [← Real.rpow_mul hM0.le]
    exact Real.rpow_le_rpow_of_exponent_le hM (morrey_gradient_exponent_le hp)
  refine hh.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hd) (by positivity)) (by positivity)

end WaveTurbulence.Analysis
