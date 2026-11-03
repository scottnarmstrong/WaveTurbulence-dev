/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleScaleIdentities
public import WaveTurbulence.Foundations.NumberTheory.PowerScaleComparison

/-! # Absorption of the optimized circle errors -/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Below the trivial-sum regime both optimized error monomials fit the B-scale. -/
theorem circle_error_monomials_le {R h U : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hU : 1 ≤ U) (hUF : U ≤ circleOscillation R h U)
    (hFU : circleOscillation R h U ≤ U ^ (5 : ℝ)) :
    circleOscillation R h U ^ (2 / 5 : ℝ) ≤ circleBScale R h U ∧
      U / Real.sqrt (circleOscillation R h U) ≤ circleBScale R h U := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hF : 0 < circleOscillation R h U := hU0.trans_le hUF
  rw [circleBScale_eq hR hh hU0]
  constructor
  · have he := rpow_mul_le_of_upper_scale (a := (2 / 5 : ℝ)) (b := 0)
      (c := (11 / 30 : ℝ)) (d := (1 / 6 : ℝ)) hU hF hFU (by norm_num) (by norm_num)
    simpa only [Real.rpow_zero, mul_one] using he
  · have he := rpow_mul_le_of_lower_scale (a := (-1 / 2 : ℝ)) (b := 1)
      (c := (11 / 30 : ℝ)) (d := (1 / 6 : ℝ)) (l := 1)
      hU hF (by simpa only [Real.rpow_one] using hUF) (by norm_num) (by norm_num)
    rw [Real.rpow_one, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
      Real.rpow_neg hF.le, ← Real.sqrt_eq_rpow] at he
    simpa only [div_eq_mul_inv, mul_comm] using he

/-- Above the error-absorption range the trivial source count already fits. -/
theorem circle_length_le_BScale {R h U : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hU : 1 ≤ U) (hUF : U ^ (5 : ℝ) ≤ circleOscillation R h U) :
    U ≤ circleBScale R h U := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hF : 0 < circleOscillation R h U :=
    (Real.rpow_pos_of_pos hU0 _).trans_le hUF
  rw [circleBScale_eq hR hh hU0]
  have he := rpow_mul_le_of_lower_scale (a := (0 : ℝ)) (b := 1)
    (c := (11 / 30 : ℝ)) (d := (1 / 6 : ℝ)) hU hF hUF (by norm_num) (by norm_num)
  simpa only [Real.rpow_zero, Real.rpow_one, one_mul] using he

/-- A source block always has transformed scale at least one. -/
theorem one_le_circleBScale {R h U : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hU : 1 ≤ U) (hUF : U ≤ circleOscillation R h U) :
    1 ≤ circleBScale R h U := by
  rw [circleBScale_eq hR hh (zero_lt_one.trans_le hU)]
  exact one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (hU.trans hUF) (by norm_num))
    (Real.one_le_rpow hU (by norm_num))

end WaveTurbulence.VdCB
