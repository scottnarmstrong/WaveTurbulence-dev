/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.WickNormalization

/-! # Geometric order constants in the actual Wick slice bound -/

public section
namespace WaveTurbulence.RegAsymp

/-- The additional delta factor per traced link is harmless uniformly
in every order; constants do not depend on the order exponent. -/
theorem wick_delta_order_budget {d n m r : ℕ} {δ K Knt : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hKnt0 : 0 ≤ Knt)
    (hdK : (2:ℝ)^d ≤ K) (hKnt : Knt ≤ K) (h : m+r = n) :
    (2^d*δ^2/4)^r*(Knt*δ/4)^m ≤ (K*δ)^n := by
  have hK0 : 0 ≤ K := (by positivity : (0:ℝ) ≤ 2^d).trans hdK
  have hδsq : δ^2 ≤ δ := by nlinarith
  have ht : 2^d*δ^2/4 ≤ K*δ := by
    calc
      _ ≤ 2^d*δ/4 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hδsq (by positivity)) (by norm_num)
      _ ≤ 2^d*δ := div_le_self (by positivity) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right hdK hδ
  have hm : Knt*δ/4 ≤ K*δ :=
    (div_le_self (mul_nonneg hKnt0 hδ) (by norm_num : (1:ℝ) ≤ 4)).trans
      (mul_le_mul_of_nonneg_right hKnt hδ)
  calc
    _ ≤ (K*δ)^r*(K*δ)^m := mul_le_mul
      (pow_le_pow_left₀ (by positivity) ht r) (pow_le_pow_left₀ (by positivity) hm m)
      (by positivity) (by positivity)
    _ = _ := by rw [← pow_add,show r+m=n by omega]

/-- The original normalization and free-vector count retain the exact
codimension power, with a single geometric source constant. -/
theorem normalized_wick_count_budget {d n m r : ℕ} {L δ γ K Knt : ℝ}
    (hL : 0 < L) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hKnt0 : 0 ≤ Knt)
    (hdK : (2:ℝ)^d ≤ K) (hKnt : Knt ≤ K) (h : m+r = n) :
    (δ/(2*L^((d:ℝ)-γ)))^(2*r)*(2^d*L^d)^r*(Knt*δ/4)^m*2^n ≤
      (2*K*δ)^n*(L^(-((d:ℝ)-2*γ)))^r := by
  have hs : (δ/(2*L^((d:ℝ)-γ)))^(2*r)*(2^d*L^d)^r =
      ((2^d*δ^2/4)*L^(-((d:ℝ)-2*γ)))^r := by
    rw [pow_mul,← mul_pow,wick_one_link_normalization hL]
  rw [hs,mul_pow]
  calc
    _ = ((2^d*δ^2/4)^r*(Knt*δ/4)^m)*2^n*(L^(-((d:ℝ)-2*γ)))^r := by ring
    _ ≤ (K*δ)^n*2^n*(L^(-((d:ℝ)-2*γ)))^r :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (wick_delta_order_budget hδ hδ1 hKnt0 hdK hKnt h) (by positivity))
        (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end WaveTurbulence.RegAsymp
