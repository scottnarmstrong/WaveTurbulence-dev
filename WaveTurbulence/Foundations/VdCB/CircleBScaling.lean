/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleDualWeightedASum

/-!
# The B-after-A³ circle scale

The actual circle frequency comparison converts the weighted dual
A-scale to `h^(11/30) R^(11/60) U^(7/20)`. This is the direct-family
scale corresponding to the transformed pair `(11/30,16/30)`.
-/

public section

namespace WaveTurbulence.VdCB

private theorem rpow_square {x : ℝ} (hx : 0 < x) (p : ℝ) :
    (x ^ 2) ^ p = x ^ (2 * p) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx.le]

/-- Pure scalar conversion of the weighted circle dual scale. -/
theorem circle_weighted_A_scale_le {R h U Y : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hU : 0 < U) (hY : 0 < Y)
    (hfrequency : R * h ^ 2 / (9 * U) ≤ Y ^ 2) :
    Real.sqrt R * h * (R * h ^ 2 / Y ^ 2) ^ ((1 : ℝ) / 30) * Y ^ (-(19 / 30) : ℝ) ≤
      9 * (h ^ ((11 : ℝ) / 30) * R ^ ((11 : ℝ) / 60) * U ^ ((7 : ℝ) / 20)) := by
  let A := R * h ^ 2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hcoeff : Real.sqrt R * h = A ^ (1 / 2 : ℝ) := by
    dsimp only [A]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hR.le, Real.sqrt_sq_eq_abs, abs_of_pos hh]
  have hmain : Real.sqrt R * h * (A / Y ^ 2) ^ ((1 : ℝ) / 30) * Y ^ (-(19 / 30) : ℝ) =
      A ^ ((8 : ℝ) / 15) * (Y ^ 2) ^ (-(7 / 20) : ℝ) := by
    rw [hcoeff, Real.div_rpow hA.le (sq_nonneg Y), rpow_square hY, rpow_square hY]
    rw [div_eq_mul_inv (A ^ ((1 : ℝ) / 30)) (Y ^ (2 * ((1 : ℝ) / 30))), ← Real.rpow_neg hY.le]
    calc
      _ = (A ^ (1 / 2 : ℝ) * A ^ ((1 : ℝ) / 30)) *
          (Y ^ (-(2 * ((1 : ℝ) / 30))) * Y ^ (-(19 / 30) : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hA, ← Real.rpow_add hY]
        norm_num only [show (1 / 2 : ℝ) + 1 / 30 = 8 / 15 by norm_num,
          show -(2 * ((1 : ℝ) / 30)) + -(19 / 30) = -(7 / 10) by norm_num,
          show (2 : ℝ) * -(7 / 20) = -(7 / 10) by norm_num]
  have hpow := Real.rpow_le_rpow_of_nonpos (div_pos hA (by positivity : 0 < 9 * U))
    hfrequency (by norm_num : (-(7 / 20) : ℝ) ≤ 0)
  have hscale : A ^ ((8 : ℝ) / 15) * (A / (9 * U)) ^ (-(7 / 20) : ℝ) =
      (9 : ℝ) ^ ((7 : ℝ) / 20) *
        (h ^ ((11 : ℝ) / 30) * R ^ ((11 : ℝ) / 60) * U ^ ((7 : ℝ) / 20)) := by
    rw [Real.div_rpow hA.le (by positivity : 0 ≤ 9 * U),
      Real.rpow_neg (by positivity : 0 ≤ 9 * U), div_inv_eq_mul]
    rw [← mul_assoc, ← Real.rpow_add hA,
      show (8 / 15 : ℝ) + -(7 / 20) = 11 / 60 by norm_num]
    dsimp only [A]
    rw [Real.mul_rpow hR.le (sq_nonneg h), rpow_square hh,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) hU.le,
      show (2 : ℝ) * (11 / 60) = 11 / 30 by norm_num]
    ring
  change Real.sqrt R * h * (A / Y ^ 2) ^ ((1 : ℝ) / 30) * Y ^ (-(19 / 30) : ℝ) ≤ _
  rw [hmain]
  calc
    _ ≤ A ^ ((8 : ℝ) / 15) * (A / (9 * U)) ^ (-(7 / 20) : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hA.le _)
    _ = _ := hscale
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 9) (by norm_num : (7 : ℝ) / 20 ≤ 1))
      (by positivity)

/-- A single actual stationary weight is also controlled by the transformed scale. -/
theorem circleDualWeight_le_B_scale {R h U Y : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hU : 0 < U) (hY : 1 ≤ Y)
    (hRY : Y ^ 2 ≤ R * h ^ 2) (hfrequency : R * h ^ 2 / (9 * U) ≤ Y ^ 2) :
    circleDualWeight R h Y ≤
      9 * (h ^ ((11 : ℝ) / 30) * R ^ ((11 : ℝ) / 60) * U ^ ((7 : ℝ) / 20)) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hp : 1 ≤ (R * h ^ 2 / Y ^ 2) ^ ((1 : ℝ) / 30) :=
    Real.one_le_rpow ((one_le_div₀ (sq_pos_of_pos hYp)).mpr hRY) (by norm_num)
  have hq : 1 ≤ Y ^ ((26 : ℝ) / 30) := Real.one_le_rpow hY (by norm_num)
  have hprod := one_le_mul_of_one_le_of_one_le hp hq
  have hpow : Y ^ (-(3 / 2) : ℝ) * Y ^ ((26 : ℝ) / 30) = Y ^ (-(19 / 30) : ℝ) := by
    rw [← Real.rpow_add hYp]
    norm_num
  have hcoeff : 0 ≤ Real.sqrt R * h * Y ^ (-(3 / 2) : ℝ) := by positivity
  calc
    _ ≤ Real.sqrt R * h * Y ^ (-(3 / 2) : ℝ) := circleDualWeight_le hh hYp le_rfl
    _ ≤ (Real.sqrt R * h * Y ^ (-(3 / 2) : ℝ)) *
        ((R * h ^ 2 / Y ^ 2) ^ ((1 : ℝ) / 30) * Y ^ ((26 : ℝ) / 30)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod hcoeff
    _ = Real.sqrt R * h * (R * h ^ 2 / Y ^ 2) ^ ((1 : ℝ) / 30) * Y ^ (-(19 / 30) : ℝ) := by
      calc
        _ = Real.sqrt R * h * (R * h ^ 2 / Y ^ 2) ^ ((1 : ℝ) / 30) *
          (Y ^ (-(3 / 2) : ℝ) * Y ^ ((26 : ℝ) / 30)) := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := circle_weighted_A_scale_le hR hh hU hYp hfrequency

/-- The weighted actual dual sum already has the transformed circle scale.
Only numerical/geometric range conditions are assumed. -/
theorem norm_sum_circleDualWeight_mul_le_B_scale (a : ℤ) (K : ℕ) (p q : ℝ)
    {R h U : ℝ} (hR : 0 < R) (hh : 0 < h) (hU : 0 < U)
    (hY : 1 ≤ (a : ℝ) + 1) (hhY : h ≤ (a : ℝ) + 1)
    (hRY : ((a : ℝ) + 1) ^ 2 ≤ R * h ^ 2) (hK : (K : ℝ) ≤ 2 * ((a : ℝ) + 1))
    (hfrequency : R * h ^ 2 / (9 * U) ≤ ((a : ℝ) + 1) ^ 2) :
    ‖∑ j ∈ Finset.range K, (circleDualWeight R h ((a : ℝ) + 1 + j) : ℂ) *
      WaveTurbulence.NumberTheory.expPhase
        (circleLatticeDualPhase R h ((a : ℝ) + 1 + j) + p * ((a : ℝ) + 1 + j) + q)‖ ≤
      154618822656 * (h ^ ((11 : ℝ) / 30) * R ^ ((11 : ℝ) / 60) * U ^ ((7 : ℝ) / 20)) := by
  have he := norm_sum_circleDualWeight_mul_add_linear_le a K p q hR hh hY hhY hRY hK
  have hs := mul_le_mul_of_nonneg_left
    (circle_weighted_A_scale_le hR hh hU (zero_lt_one.trans_le hY) hfrequency)
    (by norm_num : (0 : ℝ) ≤ 17179869184)
  apply he.trans
  convert hs using 1 <;> ring

end WaveTurbulence.VdCB
