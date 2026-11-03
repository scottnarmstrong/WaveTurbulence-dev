/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.MorreyPotential
public import WaveTurbulence.Foundations.Analysis.SquareGeometry
public import WaveTurbulence.Foundations.Analysis.MorreyScaling

/-!
# Morrey estimate on the closed unit square

The estimate uses only first derivatives and is uniform up to the boundary.
The radius parameter will be chosen as a power of `M` in TARGET (sobolev2).
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A scale-dependent Morrey bound on the unit square, with an explicit
finite kernel constant when the conjugate exponent `q` is less than two.
All norms and integrals are displayed in extended form. -/
theorem enorm_le_square_morrey {f : Mom 2 → F} (hf : ContDiff ℝ 1 f)
    {x : Mom 2} (hx : x ∈ closedSquare 0 1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ‖f x‖ₑ ≤ (ENNReal.ofReal r ^ 2)⁻¹ *
      ((∫⁻ y in closedSquare 0 1, ‖f y‖ₑ ^ p) ^ (1 / p) *
          (ENNReal.ofReal r ^ 2) ^ (1 / q) +
        ENNReal.ofReal ((3 * r) ^ 2 / 2) *
          ((ENNReal.ofReal ((3 * r) ^ (2 - q)) * rieszPowerIntegral 2 q) ^ (1 / q) *
            (∫⁻ z in closedSquare 0 1, ‖fderiv ℝ f z‖ₑ ^ p) ^ (1 / p))) := by
  have hp0 := hpq.pos
  obtain ⟨a, hxa, hsub⟩ := exists_small_closedSquare hx hr.le hr1
  have hball : closedSquare a r ⊆ Metric.ball x (3 * r) := by
    intro y hy
    have hh := norm_sub_le_two_mul_of_mem_closedSquare hxa hy
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    linarith only [hh, hr]
  have hh := enorm_mul_volume_le_morrey_ball hf (by norm_num : 0 < 2)
    (measurableSet_closedSquare a r) (convex_closedSquare a r) hxa
    (by positivity : 0 < 3 * r) hball hpq
  norm_num only [Nat.cast_ofNat, neg_one_mul] at hh
  rw [volume_closedSquare] at hh
  simp only [← sub_eq_add_neg] at hh
  have hfmono := ENNReal.rpow_le_rpow
    (lintegral_mono_set (μ := volume) (f := fun y => ‖f y‖ₑ ^ p) hsub)
    (by positivity : 0 ≤ 1 / p)
  have hdmono := ENNReal.rpow_le_rpow
    (lintegral_mono_set (μ := volume) (f := fun y => ‖fderiv ℝ f y‖ₑ ^ p) hsub)
    (by positivity : 0 ≤ 1 / p)
  have hbound := hh.trans (add_le_add
    (mul_le_mul_of_nonneg_right hfmono (by positivity))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdmono (by positivity)) (by positivity)))
  calc
    ‖f x‖ₑ = (ENNReal.ofReal r ^ 2)⁻¹ * (‖f x‖ₑ * ENNReal.ofReal r ^ 2) := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel (by positivity)
        (by finiteness), mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

/-- The constant in the unit-square Morrey estimate. It depends only on the
conjugate exponent, and is finite for `0 < q < 2`. -/
@[expose] noncomputable def squareMorreyConstant (q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((9 / 2 : ℝ) * 3 ^ ((2 - q) * (1 / q))) *
    rieszPowerIntegral 2 q ^ (1 / q)

theorem squareMorreyConstant_ne_top {q : ℝ} (hq : 0 < q) (hq2 : q < 2) :
    squareMorreyConstant q ≠ ⊤ := by
  have hI := rieszPowerIntegral_lt_top (d := 2) (by norm_num) (q := q)
    (by norm_num; linarith only [hq2])
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hq.le) hI.ne)

/-- Finiteness in the standard Morrey range `p > 2`. -/
theorem squareMorreyConstant_ne_top_of_holder {p q : ℝ} (hpq : p.HolderConjugate q)
    (hp : 2 < p) : squareMorreyConstant q ≠ ⊤ := by
  apply squareMorreyConstant_ne_top hpq.symm.pos
  rw [hpq.conjugate_eq]
  apply (div_lt_iff₀ hpq.sub_one_pos).mpr
  linarith only [hp]

/-- The usual scale-dependent Morrey estimate on the closed unit square.
For `p > 2`, take the conjugate `q = p/(p-1) < 2`. -/
theorem enorm_le_square_morrey_normalized {f : Mom 2 → F} (hf : ContDiff ℝ 1 f)
    {x : Mom 2} (hx : x ∈ closedSquare 0 1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ‖f x‖ₑ ≤ ENNReal.ofReal (r ^ (-2 / p)) *
      (∫⁻ y in closedSquare 0 1, ‖f y‖ₑ ^ p) ^ (1 / p) +
        squareMorreyConstant q * ENNReal.ofReal (r ^ (1 - 2 / p)) *
          (∫⁻ z in closedSquare 0 1, ‖fderiv ℝ f z‖ₑ ^ p) ^ (1 / p) := by
  have hh := enorm_le_square_morrey hf hx hr hr1 hpq
  rw [morrey_scale_ennreal hr hpq] at hh
  exact hh

end WaveTurbulence.Analysis
