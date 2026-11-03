/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.FifthDerivativeScale
import Mathlib.Tactic

/-!
# Fixed comparison constants in the pure fifth-derivative scale

Absolute constants in the actual circle dual derivative bounds may reduce
the common phase scale by a fixed factor. The bounded low-scale regime is
covered by the trivial actual sum; the resulting estimate keeps exactly
the `(1/30,26/30)` powers and a fully explicit comparison constant.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The pure fifth-derivative scale in the conventional pair coordinates. -/
theorem fifth_derivative_scale_pair_identity {Y T : ℝ} (hY : 0 < Y) (hT : 0 < T) :
    T^((1:ℝ)/30)*Y^((5:ℝ)/6) = (T/Y)^((1:ℝ)/30)*Y^((26:ℝ)/30) := by
  have he := rpow_mul_div_pow_identity hY hT ((26:ℝ)/30) ((1:ℝ)/30) 1
  norm_num at he
  norm_num only [show (26:ℝ)/30 = 13/15 by norm_num]
  simpa only [mul_comm] using! he.symm

/-- Actual derivative scale estimate allowing an arbitrary fixed frequency
comparison factor. This remains a theorem about derivatives and finite sums,
not a second exponent-pair notion. -/
theorem norm_exp_sum_le_of_signed_derivative_scales_with_constant
    (F : ℕ → ℝ → ℝ) (a : ℤ) (N : ℕ) {Y T c K : ℝ}
    (hY : 1 ≤ Y) (hT : 0 < T) (hK : 1 ≤ K) (hTY : Y ≤ K*T) (hNY : (N:ℝ) ≤ Y) (hc : 1 ≤ c)
    (hd : ∀ r : ℕ, r < 5 → ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      HasDerivAt (F r) (F (r+1) x) x)
    (h3 : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      F 3 x ∈ Set.Icc (-c*(T/Y^3)) (-(T/Y^3)))
    (h4 : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      F 4 x ∈ Set.Icc (T/Y^4) (c*(T/Y^4)))
    (h5 : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      F 5 x ∈ Set.Icc (-c*(T/Y^5)) (-(T/Y^5))) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (F 0 n)‖ ≤
      (K^2+16384*Real.sqrt c)*((T/Y)^((1:ℝ)/30)*Y^((26:ℝ)/30)) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  let L : ℝ := T^((1:ℝ)/30)*Y^((5:ℝ)/6)
  have hL : 0 ≤ L := by positivity
  rw [← fifth_derivative_scale_pair_identity hYp hT]
  change _ ≤ (K^2+16384*Real.sqrt c)*L
  by_cases hmain : Y^((5:ℝ)/6) ≤ T
  · apply (norm_exp_sum_le_of_three_signed_derivative_scales F a N hY hmain hNY hc hd h3 h4 h5).trans
    exact mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg K]) hL
  · have hsmall : Y ≤ K*Y^((5:ℝ)/6) :=
      hTY.trans (mul_le_mul_of_nonneg_left (le_of_not_ge hmain) hK0)
    have hfreq : 1 ≤ K*T^((1:ℝ)/30) := by
      by_cases hT1 : 1 ≤ T
      · have hp := Real.one_le_rpow hT1 (by norm_num : (0:ℝ) ≤ 1/30)
        nlinarith only [hK,hp,mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hp)]
      · have hp := Real.self_le_rpow_of_le_one hT.le (le_of_not_ge hT1)
          (by norm_num : (1:ℝ)/30 ≤ 1)
        exact (hY.trans hTY).trans (mul_le_mul_of_nonneg_left hp hK0)
    have hYbound : Y ≤ K^2*L := by
      calc
        _ ≤ K*Y^((5:ℝ)/6) := hsmall
        _ ≤ (K*Y^((5:ℝ)/6))*(K*T^((1:ℝ)/30)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hfreq
            (by positivity : 0 ≤ K*Y^((5:ℝ)/6))
        _ = _ := by dsimp only [L]; ring
    have htriv : ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (F 0 n)‖ ≤ (N:ℝ) := by
      have hn : (Finset.Ioc a (a+N)).card = N := by rw [Int.card_Ioc]; omega
      calc
        _ ≤ ∑ n ∈ Finset.Ioc a (a+N), ‖expPhase (F 0 n)‖ := norm_sum_le _ _
        _ = _ := by simp only [norm_expPhase,Finset.sum_const,nsmul_eq_mul,mul_one,hn]
    exact htriv.trans (hNY.trans (hYbound.trans (mul_le_mul_of_nonneg_right
      (by nlinarith only [Real.sqrt_nonneg c]) hL)))

end WaveTurbulence.NumberTheory
