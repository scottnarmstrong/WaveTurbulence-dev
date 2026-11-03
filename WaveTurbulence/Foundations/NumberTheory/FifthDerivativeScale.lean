/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.FifthDerivative
public import WaveTurbulence.Foundations.NumberTheory.PowerScaleComparison
import Mathlib.Tactic

/-!
# Pure fifth-derivative scale bound using three derivative orders

The third, fourth and fifth tests cover respectively `T<=Y^(5/2)`,
`Y^(5/2)<=T<=Y^(25/8)` and `T>=Y^(25/8)`. Their negative-power terms are
retained and bounded in these regimes. This proves the pure scale of the
coordinate pair `(1/30,26/30)` for actual derivative towers with the circle
dual's signed third, fourth and fifth derivatives. It is a derivative test,
not a competing definition of exponent pairs or a B-process theorem.
-/

public section

namespace WaveTurbulence.NumberTheory

private theorem derivative_terms_le_scale {M Y T a b : ℝ} (hM : 0 ≤ M) (hMY : M ≤ Y)
    (hY : 0 < Y) (hT : 0 < T) (hb : 0 ≤ b) (k : ℕ) :
    M*(T/Y^k)^a+M^b*(T/Y^k)^(-a) ≤
      T^a*Y^(1-(k:ℝ)*a)+T^(-a)*Y^(b-(k:ℝ)*(-a)) := by
  calc
    _ ≤ Y*(T/Y^k)^a+Y^b*(T/Y^k)^(-a) := add_le_add
      (mul_le_mul_of_nonneg_right hMY (by positivity))
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hM hMY hb) (by positivity))
    _ = _ := by
      have h1 := rpow_mul_div_pow_identity hY hT 1 a k
      rw [Real.rpow_one] at h1
      rw [h1,rpow_mul_div_pow_identity hY hT b (-a) k]

private theorem finish_derivative_scale {t D p q L c : ℝ}
    (ht : t ≤ D*(p+q)) (hD0 : 0 ≤ D) (hD : D ≤ 8192*Real.sqrt c)
    (hp : p ≤ L) (hq : q ≤ L) (hL : 0 ≤ L) : t ≤ 16384*Real.sqrt c*L := by
  calc
    _ ≤ D*(p+q) := ht
    _ ≤ D*(2*L) := mul_le_mul_of_nonneg_left (by linarith only [hp,hq]) hD0
    _ ≤ (8192*Real.sqrt c)*(2*L) := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = _ := by ring

/-- Pure derivative scale estimate for the circle dual sign pattern.
The phase length `N` may be any integer subwindow with `N<=Y`; constants
are uniform in that subwindow, the integer origin, and additive linear terms. -/
theorem norm_exp_sum_le_of_three_signed_derivative_scales
    (F : ℕ → ℝ → ℝ) (a : ℤ) (N : ℕ) {Y T c : ℝ}
    (hY : 1 ≤ Y) (hTY : Y^((5:ℝ)/6) ≤ T) (hNY : (N:ℝ) ≤ Y) (hc : 1 ≤ c)
    (hd : ∀ r : ℕ, r < 5 → ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      HasDerivAt (F r) (F (r+1) x) x)
    (h3 : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      F 3 x ∈ Set.Icc (-c*(T/Y^3)) (-(T/Y^3)))
    (h4 : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      F 4 x ∈ Set.Icc (T/Y^4) (c*(T/Y^4)))
    (h5 : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      F 5 x ∈ Set.Icc (-c*(T/Y^5)) (-(T/Y^5))) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (F 0 n)‖ ≤
      16384*Real.sqrt c*(T^((1:ℝ)/30)*Y^((5:ℝ)/6)) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hTp : 0 < T := (Real.rpow_pos_of_pos hYp _).trans_le hTY
  let L : ℝ := T^((1:ℝ)/30)*Y^((5:ℝ)/6)
  have hL : 0 ≤ L := by positivity
  change _ ≤ 16384*Real.sqrt c*L
  by_cases hlow : T ≤ Y^((5:ℝ)/2)
  · have ht := van_der_corput_third_derivative_tower_of_neg F a N
      (div_pos hTp (pow_pos hYp 3)) hc (fun r hr => hd r (by omega)) h3
    have hterms := derivative_terms_le_scale (Nat.cast_nonneg N) hNY hYp hTp
      (by norm_num : (0:ℝ) ≤ 1/2) (a := (1:ℝ)/6) 3
    norm_num at hterms
    have hbound := ht.trans (mul_le_mul_of_nonneg_left hterms (by positivity : 0 ≤ 12*Real.sqrt c))
    apply finish_derivative_scale hbound (by positivity)
      (by nlinarith only [Real.sqrt_nonneg c]) _ _ hL
    · exact rpow_mul_le_of_upper_scale hY hTp hlow (by norm_num) (by norm_num)
    · simpa only [Real.rpow_one] using
        (rpow_mul_le_of_lower_scale hY hTp hTY (a := -((1:ℝ)/6)) (b := 1)
          (c := (1:ℝ)/30) (d := (5:ℝ)/6) (by norm_num) (by norm_num))
  · by_cases hmid : T ≤ Y^((25:ℝ)/8)
    · have ht := van_der_corput_fourth_derivative_tower F a N
        (div_pos hTp (pow_pos hYp 4)) hc (fun r hr => hd r (by omega)) h4
      have hterms := derivative_terms_le_scale (Nat.cast_nonneg N) hNY hYp hTp
        (by norm_num : (0:ℝ) ≤ 3/4) (a := (1:ℝ)/14) 4
      norm_num at hterms
      have hbound := ht.trans (mul_le_mul_of_nonneg_left hterms (by positivity : 0 ≤ 256*Real.sqrt c))
      apply finish_derivative_scale hbound (by positivity)
        (by nlinarith only [Real.sqrt_nonneg c]) _ _ hL
      · exact rpow_mul_le_of_upper_scale hY hTp hmid (by norm_num) (by norm_num)
      · exact rpow_mul_le_of_lower_scale hY hTp (le_of_not_ge hlow) (by norm_num) (by norm_num)
    · have ht := van_der_corput_fifth_derivative_tower_of_neg F a N
        (div_pos hTp (pow_pos hYp 5)) hc hd h5
      have hterms := derivative_terms_le_scale (Nat.cast_nonneg N) hNY hYp hTp
        (by norm_num : (0:ℝ) ≤ 7/8) (a := (1:ℝ)/30) 5
      norm_num at hterms
      have hbound := ht.trans (mul_le_mul_of_nonneg_left hterms (by positivity : 0 ≤ 8192*Real.sqrt c))
      apply finish_derivative_scale hbound (by positivity) le_rfl _ _ hL
      · exact le_rfl
      · exact rpow_mul_le_of_lower_scale hY hTp (le_of_not_ge hmid) (by norm_num) (by norm_num)

end WaveTurbulence.NumberTheory
