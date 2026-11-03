/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleBPreEstimate
public import WaveTurbulence.Foundations.VdCB.CircleErrorOptimization
public import WaveTurbulence.Foundations.VdCB.CircleShortScales
public import WaveTurbulence.Foundations.VdCB.SecondDerivativeSum

/-! # The actual circle source bound for the transformed exponent pair

The bound is uniform over real centers, harmonics at least one, and
all subintervals of a dyadic block clipped at the octant boundary.
-/

public section

open Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Explicit constant for the actual circle B-after-A³ estimate. -/
@[expose] noncomputable def circleBConstant : ℝ := 154618824000 + 16 * Real.pi

/-- The actual source estimate, with no assumed exponential-sum bounds and
no free error parameters. Integral endpoints lie inside the source block. -/
theorem norm_sum_circleColumnPhase_le_BScale {R h U c : ℝ}
    (hU : 1 ≤ U) (hUR : 3 * U ≤ R) (hh : 1 ≤ h)
    {a b : ℕ} (hab : a ≤ b)
    (ha : R + c - 2 * U ≤ a) (hb : (b : ℝ) ≤ R + c - U)
    (haOct : R + c - R * (1 - 1 / Real.sqrt 2) ≤ a) :
    ‖∑ n ∈ Finset.Ico a b, expPhase (circleColumnPhase R h ((n : ℝ) + 1 - c))‖ ≤
      circleBConstant * circleBScale R h U := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have hh0 : 0 < h := zero_lt_one.trans_le hh
  have hUF := le_circleOscillation hU (by linarith only [hUR, hU0] : U ≤ R) hh
  have hF : 0 < circleOscillation R h U := hU0.trans_le hUF
  have hB1 := one_le_circleBScale hR hh0 hU hUF
  have hB0 : 0 ≤ circleBScale R h U := zero_le_one.trans hB1
  have hlen : (b : ℝ) - a ≤ U := by linarith only [ha, hb]
  by_cases hlarge : U ^ (5 : ℝ) ≤ circleOscillation R h U
  · have hUB := circle_length_le_BScale hR hh0 hU hlarge
    have htriv : ‖∑ n ∈ Finset.Ico a b, expPhase (circleColumnPhase R h ((n : ℝ) + 1 - c))‖ ≤ U := by
      calc
        _ ≤ ∑ n ∈ Finset.Ico a b, ‖expPhase (circleColumnPhase R h ((n : ℝ) + 1 - c))‖ := norm_sum_le _ _
        _ = (b : ℝ) - a := by
          simp only [norm_expPhase, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico]
          exact Nat.cast_sub hab
        _ ≤ _ := hlen
    exact htriv.trans (hUB.trans (le_mul_of_one_le_left hB0 (by unfold circleBConstant; have := Real.pi_pos; linarith)))
  have hmon := circle_error_monomials_le hR hh0 hU hUF (le_of_not_ge hlarge)
  let r := U / circleOscillation R h U ^ (2 / 5 : ℝ)
  let μ := circleCurvatureLower R h U
  let t := Real.sqrt μ
  have hr : 0 < r := by dsimp only [r]; positivity
  have hμ : 0 < μ := by dsimp only [μ, circleCurvatureLower]; positivity
  have ht : 0 < t := Real.sqrt_pos.mpr hμ
  by_cases hinner : (a : ℝ) + r ≤ b - r
  · have he := norm_sum_circleColumnPhase_le_BScale_add_error hU hUR hh0 hr ht hab ha hb haOct hinner
    have herr := circleBError_optimized_le hR hU hUF
    have hcoeff : 0 ≤ 8 * Real.pi + 400 := by positivity
    have hsum := mul_le_mul_of_nonneg_left (add_le_add hmon.1 hmon.2) hcoeff
    calc
      _ ≤ 154618822665 * circleBScale R h U + circleBError R h U r t := he
      _ ≤ 154618822665 * circleBScale R h U +
          (8 * Real.pi + 400) * (circleOscillation R h U ^ (2 / 5 : ℝ) +
            U / Real.sqrt (circleOscillation R h U)) := add_le_add le_rfl herr
      _ ≤ 154618822665 * circleBScale R h U + (8 * Real.pi + 400) *
          (circleBScale R h U + circleBScale R h U) := add_le_add le_rfl hsum
      _ ≤ _ := by unfold circleBConstant; nlinarith only [hB0]
  let F := circleColumnExtension R h U hU0 c
  have hF : ContDiff ℝ 2 F := (contDiff_circleColumnExtension hU0 hUR h c).of_le (by simp)
  have hscale : circleCurvatureUpper R h U = 8 * μ := by
    rw [circleCurvatureUpper_eq hR hU0]
    dsimp only [μ]
    rw [circleCurvatureLower_eq hR hU0]
    ring
  have hcurv (x : ℝ) (hx : x ∈ Icc (a : ℝ) b) : deriv (deriv F) x ∈ Icc (-(8 * μ)) (-μ) := by
    have hc := (circleColumnExtension_curvature_bounds hU0 hUR hh0
      (column_interval_reflection_mem ha hb hx)).1
    change μ ≤ -deriv (deriv F) x ∧ -deriv (deriv F) x ≤ circleCurvatureUpper R h U at hc
    rw [hscale] at hc
    constructor <;> linarith only [hc.1, hc.2]
  have hs := norm_sum_expPhase_le_of_second_deriv_neg hF hab hμ (by norm_num : (1 : ℝ) ≤ 8) hcurv
  have hsource : (∑ n ∈ Finset.Ico a b, expPhase (F ((n : ℝ) + 1))) =
      ∑ n ∈ Finset.Ico a b, expPhase (circleColumnPhase R h ((n : ℝ) + 1 - c)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hx : (n : ℝ) + 1 ∈ Icc (a : ℝ) b := by
      constructor
      · exact_mod_cast (show a ≤ n + 1 by omega)
      · exact_mod_cast (show n + 1 ≤ b by omega)
    dsimp only [F]
    rw [(circleColumnExtension_eventuallyEq (R := R) (h := h) (c := c) hU0
      (column_interval_reflection_mem ha hb hx)).eq_of_nhds]
  rw [hsource] at hs
  have hshort : (b : ℝ) - a ≤ 2 * r := by linarith only [hinner]
  have hshort' := mul_le_mul_of_nonneg_right hshort ht.le
  have hrt := circle_radius_mul_sqrt_curvature_le hR hU hUF
  have hit := inv_sqrt_circleCurvatureLower_le hR hh0 hU0
  have hrtB : r * t ≤ circleBScale R h U := hrt.trans hmon.1
  have hitB : 1 / t ≤ 3 * circleBScale R h U := by
    have hm := mul_le_mul_of_nonneg_left hmon.2 (by norm_num : (0 : ℝ) ≤ 3)
    have hi : 1 / t ≤ 3 * (U / Real.sqrt (circleOscillation R h U)) := by
      simpa only [mul_div_assoc] using hit
    exact hi.trans hm
  have hsmall : ‖∑ n ∈ Finset.Ico a b, expPhase (circleColumnPhase R h ((n : ℝ) + 1 - c))‖ ≤
      153 * circleBScale R h U := by
    change _ ≤ _ at hs
    change (b : ℝ) - a ≤ 2 * r at hshort
    change ((b : ℝ) - a) * t ≤ 2 * r * t at hshort'
    change _ ≤ 8 * (8 * ((b : ℝ) - a) * t + 1 / t) + 1 at hs
    nlinarith only [hs, hshort', hrtB, hitB, hB1]
  apply hsmall.trans
  apply mul_le_mul_of_nonneg_right _ hB0
  unfold circleBConstant
  have := Real.pi_pos
  linarith

end WaveTurbulence.VdCB
