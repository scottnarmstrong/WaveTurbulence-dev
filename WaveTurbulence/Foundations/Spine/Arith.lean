/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! # The final exponent arithmetic of the coarse spliced estimate (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open Finset

theorem final_arith {ι : Type} [Fintype ι] (d : ℕ) (hd : 3 ≤ d) (γ η δ x L C1 : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 1 ≤ L) (hC1 : 1 ≤ C1) (hη0 : 0 ≤ η) (hηx : 4 * η ≤ x) (hη1 : η ≤ 1)
    (m inc : ι → ℕ) (a E Inc : ℕ)
    (hSA : Inc ≤ 4 * ∑ i, inc i + 20 * E) (hSB : Fintype.card ι ≤ 2 * E)
    (hSC : a + Fintype.card ι ≤ 8 * E) :
    (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (a + Fintype.card ι) * (3 * L) ^ (2 * d * (a + Fintype.card ι)) *
        ∏ i, (C1 * (C1 * δ) ^ (m i) * L ^ (-x * (inc i : ℝ) + 20 * (d : ℝ))) ≤
      (C1 * 3 ^ (2 * d) * Real.sqrt δ) ^ (∑ i, (2 * m i + 2) + a) *
        L ^ (-η * (Inc : ℝ) + 80 * (d : ℝ) * (E : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hC0 : 0 < C1 := by linarith
  set q := Fintype.card ι with hq
  set S1 := ∑ i, m i with hS1
  set J := ∑ i, inc i with hJ
  set r := a + q with hr
  set s := Real.sqrt δ with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hδ
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sqrt_le_one.mpr hδ1
  have hδs : δ = s ^ 2 := by rw [hs, Real.sq_sqrt hδ.le]
  have hn : ∑ i, (2 * m i + 2) + a = 2 * S1 + 2 * q + a := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp [hS1, hq]; ring
  -- the product over ladders
  have hprod : ∏ i, (C1 * (C1 * δ) ^ (m i) * L ^ (-x * (inc i : ℝ) + 20 * (d : ℝ))) =
      C1 ^ q * (C1 * δ) ^ S1 * L ^ (-x * (J : ℝ) + 20 * (d : ℝ) * (q : ℝ)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
      ← Real.rpow_sum_of_pos hL0]
    congr 2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hJ]
    push_cast
    simp [hq]
    ring
  rw [hprod, hn]
  -- compare pieces
  have hLd : 0 < L ^ ((d : ℝ) - γ) := Real.rpow_pos_of_pos hL0 _
  have hLp : (L ^ ((d : ℝ) - γ)) ^ r = L ^ (((d : ℝ) - γ) * (r : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  have hLpos : 0 < L ^ (((d : ℝ) - γ) * (r : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hcoup : (δ / (2 * L ^ ((d : ℝ) - γ))) ^ r ≤ δ ^ r * L ^ (-(((d : ℝ) - γ) * (r : ℝ))) := by
    rw [div_pow, mul_pow, hLp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
    have h2 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    apply div_le_div_of_nonneg_left (by positivity) hLpos
    nlinarith
  have h3L : (3 * L) ^ (2 * d * r) = 3 ^ (2 * d * r) * L ^ ((2 * (d : ℝ) * r)) := by
    rw [mul_pow, ← Real.rpow_natCast L (2 * d * r)]
    congr 2
    push_cast; ring
  -- L powers
  have hLsum : L ^ (-(((d : ℝ) - γ) * (r : ℝ))) * L ^ ((2 * (d : ℝ) * r)) *
      L ^ (-x * (J : ℝ) + 20 * (d : ℝ) * (q : ℝ)) =
      L ^ (-(((d : ℝ) - γ) * (r : ℝ)) + 2 * (d : ℝ) * r + (-x * (J : ℝ) + 20 * (d : ℝ) * (q : ℝ))) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
  have hexp : -(((d : ℝ) - γ) * (r : ℝ)) + 2 * (d : ℝ) * r + (-x * (J : ℝ) + 20 * (d : ℝ) * (q : ℝ)) ≤
      -η * (Inc : ℝ) + 80 * (d : ℝ) * (E : ℝ) := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hSA' : (Inc : ℝ) ≤ 4 * (J : ℝ) + 20 * (E : ℝ) := by exact_mod_cast hSA
    have hSB' : (q : ℝ) ≤ 2 * (E : ℝ) := by exact_mod_cast hSB
    have hSC' : (r : ℝ) ≤ 8 * (E : ℝ) := by rw [hr]; exact_mod_cast hSC
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have h1 : η * (Inc : ℝ) ≤ x * J + 20 * E := by
      have : η * (Inc : ℝ) ≤ η * (4 * J + 20 * E) := mul_le_mul_of_nonneg_left hSA' hη0
      nlinarith
    have h2 : ((d : ℝ) + γ) * r ≤ 16 * d * E := by
      have : ((d : ℝ) + γ) ≤ 2 * d := by linarith
      nlinarith
    have h3 : 20 * (d : ℝ) * q ≤ 40 * d * E := by nlinarith
    nlinarith
  have hLle : L ^ (-(((d : ℝ) - γ) * (r : ℝ)) + 2 * (d : ℝ) * r + (-x * (J : ℝ) + 20 * (d : ℝ) * (q : ℝ))) ≤
      L ^ (-η * (Inc : ℝ) + 80 * (d : ℝ) * (E : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL hexp
  -- constants and powers of delta
  have hn_ge : r ≤ 2 * S1 + 2 * q + a := by rw [hr]; omega
  have hn_ge2 : q + S1 ≤ 2 * S1 + 2 * q + a := by omega
  have hconst : δ ^ r * (C1 * δ) ^ S1 * C1 ^ q * 3 ^ (2 * d * r) ≤
      (C1 * 3 ^ (2 * d) * s) ^ (2 * S1 + 2 * q + a) := by
    have e1 : δ ^ r * (C1 * δ) ^ S1 * C1 ^ q * 3 ^ (2 * d * r) =
        (C1 ^ S1 * C1 ^ q) * 3 ^ (2 * d * r) * δ ^ (r + S1) := by
      rw [mul_pow, pow_add]; ring
    have e2 : (C1 * 3 ^ (2 * d) * s) ^ (2 * S1 + 2 * q + a) =
        C1 ^ (2 * S1 + 2 * q + a) * (3 ^ (2 * d)) ^ (2 * S1 + 2 * q + a) * s ^ (2 * S1 + 2 * q + a) := by
      rw [mul_pow, mul_pow]
    rw [e1, e2]
    have c1 : C1 ^ S1 * C1 ^ q ≤ C1 ^ (2 * S1 + 2 * q + a) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hC1 (by omega)
    have c2 : (3 : ℝ) ^ (2 * d * r) ≤ (3 ^ (2 * d)) ^ (2 * S1 + 2 * q + a) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left (2 * d) hn_ge)
    have c3 : δ ^ (r + S1) ≤ s ^ (2 * S1 + 2 * q + a) := by
      rw [hδs, ← pow_mul]
      exact pow_le_pow_of_le_one hs0.le hs1 (by rw [hr]; omega)
    have hC1p : 0 ≤ C1 ^ S1 * C1 ^ q := by positivity
    exact mul_le_mul (mul_le_mul c1 c2 (by positivity) (by positivity)) c3 (by positivity) (by positivity)
  -- assemble
  have h3L : (3 * L) ^ (2 * d * r) = 3 ^ (2 * d * r) * L ^ ((2 * (d : ℝ) * r)) := by
    rw [mul_pow, ← Real.rpow_natCast L (2 * d * r)]
    congr 2
    push_cast; ring
  calc (δ / (2 * L ^ ((d : ℝ) - γ))) ^ r * (3 * L) ^ (2 * d * r) *
        (C1 ^ q * (C1 * δ) ^ S1 * L ^ (-x * (J : ℝ) + 20 * (d : ℝ) * (q : ℝ)))
      ≤ (δ ^ r * L ^ (-(((d : ℝ) - γ) * (r : ℝ)))) * (3 ^ (2 * d * r) * L ^ ((2 * (d : ℝ) * r))) *
        (C1 ^ q * (C1 * δ) ^ S1 * L ^ (-x * (J : ℝ) + 20 * (d : ℝ) * (q : ℝ))) := by
        rw [h3L]; gcongr
    _ = (δ ^ r * (C1 * δ) ^ S1 * C1 ^ q * 3 ^ (2 * d * r)) *
        (L ^ (-(((d : ℝ) - γ) * (r : ℝ))) * L ^ ((2 * (d : ℝ) * r)) *
          L ^ (-x * (J : ℝ) + 20 * (d : ℝ) * (q : ℝ))) := by ring
    _ ≤ (C1 * 3 ^ (2 * d) * s) ^ (2 * S1 + 2 * q + a) * L ^ (-η * (Inc : ℝ) + 80 * (d : ℝ) * (E : ℝ)) := by
        rw [hLsum]
        exact mul_le_mul hconst hLle (by positivity) (by positivity)

end WaveTurbulence.CoarseSpliced
