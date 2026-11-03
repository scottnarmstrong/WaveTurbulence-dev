/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.ImprovedPositiveShellThreshold

/-! # The strict two-thirds saving for fixed-sum pair fibers -/

public section
namespace WaveTurbulence.CountLemmas

/-- If the integer squared-energy tolerance is at most `L^a`, `a≤1/2`,
the uniform planar threshold is `L^(81*(2+a)/244)`. -/
theorem positive_atom_shell_improved_power_bound {d : ℕ} {L τ a : ℝ}
    (hL : 1 ≤ L) (hτ : 0 ≤ τ) (hW : 1 ≤ τ*L^2)
    (ha : a ≤ 1/2) (hWa : τ*L^2 ≤ L^a) (b c : Mom (d+2))
    (nk : Fin (d+2) → ℤ) (β : ℝ) :
    ((atomPairSet L b c nk β τ 1).ncard : ℝ) ≤
      (3^d*(6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002))*L^((d : ℝ)+81*(2+a)/244) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let U := L^(81*(2+a)/244)
  have hWU : τ*L^2 ≤ U := hWa.trans
    (Real.rpow_le_rpow_of_exponent_le hL (by linarith only [ha]))
  have hbudget : L^2*(τ*L^2) ≤ U^((244 : ℝ)/81) := by
    calc
      _ ≤ L^2*L^a := mul_le_mul_of_nonneg_left hWa (sq_nonneg L)
      _ = L^(2+a) := by rw [← Real.rpow_two,← Real.rpow_add hLp]
      _ = U^((244 : ℝ)/81) := by
        dsimp only [U]
        rw [← Real.rpow_mul hLp.le]
        congr 1
        norm_num
        ring
  have hc := positive_atom_shell_improved_threshold_bound hLp hτ hW hWU hbudget b c nk β
  have hbox : (2*L+1)^d ≤ 3^d*L^d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) d
  calc
    _ ≤ (2*L+1)^d*(6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002)*U := hc
    _ ≤ (3^d*L^d)*(6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002)*U :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbox (by positivity)) (by dsimp only [U]; positivity)
    _ = _ := by
      calc
        _ = (3^d*(6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002))*(L^(d : ℝ)*L^(81*(2+a)/244)) := by rw [Real.rpow_natCast]; ring
        _ = _ := by rw [← Real.rpow_add hLp]

end WaveTurbulence.CountLemmas
