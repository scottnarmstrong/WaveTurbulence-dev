/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Uniform constants in the elementary low-γ pair estimate -/

public section
namespace WaveTurbulence.CountLemmas

/-- The elementary radial bound is `O(τ² L^(2d)/P)` when `τL≥1`.
All constants are explicit and independent of τ and P. -/
theorem coarse_pair_low_scale_bound (d : ℕ) (hd : 2 ≤ d)
    {L τ P K U : ℝ} (hL : 1 ≤ L) (hτL : 1 ≤ τ*L) (hP : 0 < P) (hP1 : P ≤ 1)
    (hK : 0 ≤ K) (hU : U ≤ K*τ*L/P) :
    15^d*L^d+12*((d : ℝ)+1)*(3^(d-1)*L^(d-1))^2*U*(1+τ*L) ≤
    (15^d+24*((d : ℝ)+1)*(3^(d-1))^2*K)*(τ^2*L^(2*d)/P) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hτ : 0 < τ := (mul_pos_iff_of_pos_right hLp).mp (zero_lt_one.trans_le hτL)
  have hid : L^(2*d) = (L^(d-1))^2*L^2 := by
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  have hdim : L^d ≤ (L^(d-1))^2 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hL (by omega)
  have hfac : 1 ≤ τ^2*L^2/P := by
    apply (le_div_iff₀ hP).mpr
    have hh : 1 ≤ (τ*L)^2 := by nlinarith only [hτL]
    nlinarith only [hh,hP1]
  have hspace : L^d ≤ τ^2*L^(2*d)/P := by
    apply hdim.trans
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hfac (by positivity : 0 ≤ (L^(d-1))^2)
    convert hh using 1 <;> ring
  have htail : 1+τ*L ≤ 2*τ*L := by linarith only [hτL]
  have hmain : 12*((d : ℝ)+1)*(3^(d-1)*L^(d-1))^2*U*(1+τ*L) ≤
      (24*((d : ℝ)+1)*(3^(d-1))^2*K)*(τ^2*L^(2*d)/P) := by
    have hh := mul_le_mul hU htail (by positivity : 0 ≤ 1+τ*L) (by positivity : 0 ≤ K*τ*L/P)
    have hm := mul_le_mul_of_nonneg_left hh
      (by positivity : 0 ≤ 12*((d : ℝ)+1)*(3^(d-1)*L^(d-1))^2)
    rw [hid]
    convert hm using 1 <;> ring
  have hh := add_le_add (mul_le_mul_of_nonneg_left hspace (by positivity : 0 ≤ (15 : ℝ)^d)) hmain
  convert hh using 1; ring

/-- The same-sign fixed-sum fiber bound has the same low-γ scaling. -/
theorem sum_pair_low_scale_bound (n : ℕ) {L τ P K U M : ℝ}
    (hL : 1 ≤ L) (hτL : 1 ≤ τ*L) (hP : 0 < P) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hU0 : 0 ≤ U) (hU : U ≤ K*τ*L/P) :
    (4*L+1)^(n+1)*U*((2*L+1)^n*M*(2*τ*L^2+L)) ≤
      (3*5^(n+1)*3^n*M*K)*(τ^2*L^(2*(n+2))/P) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hτ : 0 < τ := (mul_pos_iff_of_pos_right hLp).mp (zero_lt_one.trans_le hτL)
  have hx : (4*L+1)^(n+1) ≤ (5 : ℝ)^(n+1)*L^(n+1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) _
  have hy : (2*L+1)^n ≤ (3 : ℝ)^n*L^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) _
  have ht : 2*τ*L^2+L ≤ 3*τ*L^2 := by
    have hh := mul_le_mul_of_nonneg_right hτL hLp.le
    nlinarith only [hh]
  have htail : (2*L+1)^n*M*(2*τ*L^2+L) ≤ (3 : ℝ)^n*L^n*M*(3*τ*L^2) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hy hM) ht (by positivity) (by positivity)
  have hh := mul_le_mul (mul_le_mul hx hU hU0 (by positivity))
    htail (by positivity) (by positivity)
  have hid : L^(2*(n+2)) = L^(n+1)*L^n*L^3 := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  rw [hid]
  convert hh using 1; ring

end WaveTurbulence.CountLemmas
