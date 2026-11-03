/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.CircleWeightedDual
import Mathlib.Tactic

/-!
# Weighted actual circle dual estimates on consecutive integer intervals

The actual source stationary frequencies form a closed integer interval.
This interface retains its endpoints and derives the A-scale admissibility
from the upper source-frequency scale and `U>=1`.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The weighted dual estimate on a closed consecutive integer window of
length at most twice its first frequency. -/
theorem norm_sum_weighted_circle_dual_Icc_le_of_length (L V : ℤ) (p q : ℝ)
    {R h U : ℝ} (hR : 0 < R) (hh : 0 < h) (hU : 1 ≤ U)
    (hL : 1 ≤ (L:ℝ)) (hhL : h ≤ L) (hLV : L ≤ V)
    (hwidth : (V:ℝ)-(L:ℝ)+1 ≤ 2*(L:ℝ))
    (hV : (V:ℝ) ≤ h*Real.sqrt (R/U)) (hscale : (h*Real.sqrt (R/U))/8 ≤ L) :
    ‖∑ n ∈ Finset.Icc L V,
      (Real.sqrt R*h*(h^2+(n:ℝ)^2)^(-((3:ℝ)/4))) •
        expPhase (VdCB.circleLatticeDualPhase R h n+p*(n:ℝ)+q)‖ ≤
      137438953472*(h^((11:ℝ)/30)*R^((11:ℝ)/60)*U^((7:ℝ)/20)) := by
  let N : ℕ := (V-L+1).toNat
  have hNz : (N:ℤ) = V-L+1 := Int.toNat_of_nonneg (by omega)
  have hNr : (N:ℝ) = (V:ℝ)-(L:ℝ)+1 := by exact_mod_cast hNz
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hLp : (0:ℝ) < L := zero_lt_one.trans_le hL
  let B : ℝ := h*Real.sqrt (R/U)
  have hBp : 0 < B := mul_pos hh (Real.sqrt_pos.mpr (div_pos hR hUp))
  have hLB : (L:ℝ) ≤ B := (by exact_mod_cast hLV : (L:ℝ) ≤ V).trans hV
  have hBsq : B^2 ≤ R*h^2 := by
    have hdiv : R/U ≤ R := div_le_self hR.le hU
    have hm := mul_le_mul_of_nonneg_left hdiv (sq_nonneg h)
    dsimp only [B]
    rw [mul_pow,Real.sq_sqrt (div_pos hR hUp).le]
    nlinarith only [hm]
  have hYsq : (L:ℝ)^2 ≤ R*h^2 :=
    (pow_le_pow_left₀ hLp.le hLB 2).trans hBsq
  have heq : Finset.Ioc (L-1) ((L-1)+(N:ℤ)) = Finset.Icc L V := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hb : ((L-1:ℤ):ℝ)+N+2 ≤ 4*(L:ℝ) := by
    push_cast
    linarith only [hNr,hwidth,hL]
  have ha : (L:ℝ) ≤ ((L-1:ℤ):ℝ)+1 := by push_cast; linarith
  have hNY : (N:ℝ) ≤ 2*(L:ℝ) := by linarith only [hNr,hwidth]
  have he := norm_sum_weighted_circleLatticeDualPhase_le_endpoint_factor (L-1) N p q
    hR hh hL hUp hhL hYsq ha hb hNY (by norm_num : (1:ℝ) ≤ 8) hscale
  rw [heq] at he
  norm_num only [show (17179869184:ℝ)*8 = 137438953472 by norm_num] at he
  exact he

end WaveTurbulence.NumberTheory
