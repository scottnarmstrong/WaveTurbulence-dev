/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleLatticeRegularity

/-!
# Actual derivative tower of the circle Legendre phase

All tower entries are actual iterated derivatives, at every order.
The third, fourth and fifth entries are converted to the literal quotient
form consumed by the landed A-process theorem.
-/

public section

namespace WaveTurbulence.VdCB

/-- The actual full derivative tower of the circle Legendre phase. -/
@[expose] noncomputable def circleDualTower (R h : ℝ) (r : ℕ) : ℝ → ℝ :=
  iteratedDeriv r (circleDualPhase R h)

theorem hasDerivAt_circleDualTower (R : ℝ) {h : ℝ} (hh : 0 < h) (r : ℕ) (x : ℝ) :
    HasDerivAt (circleDualTower R h r) (circleDualTower R h (r + 1) x) x := by
  unfold circleDualTower
  rw [iteratedDeriv_succ]
  have hf : ContDiff ℝ (r + 1 : ℕ) (circleDualPhase R h) :=
    (contDiff_circleDualPhase R hh).of_le (by simp)
  exact (hf.differentiable_iteratedDeriv' r x).hasDerivAt

private theorem circleDualTower_three (R : ℝ) {h : ℝ} (hh : 0 < h) :
    circleDualTower R h 3 = circleDualThird R h := by
  have h1 : deriv (circleDualPhase R h) = circleDualFirst R h :=
    funext fun x => (hasDerivAt_circleDualPhase R hh x).deriv
  have h2 : deriv (circleDualFirst R h) = circleDualSecond R h :=
    funext fun x => (hasDerivAt_circleDualFirst R hh x).deriv
  have h3 : deriv (circleDualSecond R h) = circleDualThird R h :=
    funext fun x => (hasDerivAt_circleDualSecond R hh x).deriv
  simp only [circleDualTower, iteratedDeriv_succ, iteratedDeriv_zero, h1, h2, h3]

private theorem circleDualTower_four (R : ℝ) {h : ℝ} (hh : 0 < h) :
    circleDualTower R h 4 = circleDualFourth R h := by
  have h3 := circleDualTower_three R hh
  have h4 : deriv (circleDualThird R h) = circleDualFourth R h :=
    funext fun x => (hasDerivAt_circleDualThird R hh x).deriv
  unfold circleDualTower
  rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ]
  rw [show iteratedDeriv 3 (circleDualPhase R h) = circleDualThird R h from h3, h4]

private theorem rpow_negative_half_integer {D : ℝ} (hD : 0 < D) (k : ℕ) :
    D ^ (-((k : ℝ) + 1 / 2)) = (D ^ k * Real.sqrt D)⁻¹ := by
  rw [Real.rpow_neg hD.le, Real.rpow_add hD, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

theorem circleDualTower_three_quotient (R : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    circleDualTower R h 3 x = -((3 * R * h ^ 2 * x) / ((h ^ 2 + x ^ 2) ^ 2 * Real.sqrt (h ^ 2 + x ^ 2))) := by
  have hD : 0 < h ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)
  rw [circleDualTower_three R hh]
  unfold circleDualThird
  rw [show -(5 / 2 : ℝ) = -((2 : ℕ) + (1 / 2 : ℝ)) by norm_num,
    rpow_negative_half_integer hD 2]
  ring

theorem circleDualTower_four_quotient (R : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    circleDualTower R h 4 x = (3 * R * h ^ 2 * (4 * x ^ 2 - h ^ 2)) /
      ((h ^ 2 + x ^ 2) ^ 3 * Real.sqrt (h ^ 2 + x ^ 2)) := by
  have hD : 0 < h ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)
  rw [circleDualTower_four R hh]
  unfold circleDualFourth
  rw [show -(7 / 2 : ℝ) = -((3 : ℕ) + (1 / 2 : ℝ)) by norm_num,
    rpow_negative_half_integer hD 3]
  ring

theorem circleDualTower_five_quotient (R : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    circleDualTower R h 5 x = -((15 * R * h ^ 2 * x * (4 * x ^ 2 - 3 * h ^ 2)) /
      ((h ^ 2 + x ^ 2) ^ 4 * Real.sqrt (h ^ 2 + x ^ 2))) := by
  have hD : 0 < h ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)
  rw [circleDualTower, iteratedDeriv_five_circleDualPhase R hh]
  unfold circleDualFifth
  rw [show -(9 / 2 : ℝ) = -((4 : ℕ) + (1 / 2 : ℝ)) by norm_num,
    rpow_negative_half_integer hD 4]
  ring

end WaveTurbulence.VdCB
