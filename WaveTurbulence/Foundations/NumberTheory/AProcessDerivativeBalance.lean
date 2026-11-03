/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.AProcessTwoPowersCutoff
import Mathlib.Tactic

/-!
# Balancing an A-step for higher derivative tests

Both terms of the lower-order derivative test survive the A-step. The
new exponents are `alpha/(2*alpha+2)` and `(b+1)/2`. This module proves the
balanced-cutoff regime from actual finite differenced sums.
-/

public section

namespace WaveTurbulence.NumberTheory

private theorem le_scaled_sum_of_sq_le {t x y C : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hC : 1 ≤ C) (hs : t^2 ≤ C*(x^2+y^2)) : t ≤ C*(x+y) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hCC : C ≤ C^2 := by nlinarith only [hC]
  have hb : C*(x^2+y^2) ≤ (C*(x+y))^2 := by
    calc
      _ ≤ C^2*(x^2+y^2) := mul_le_mul_of_nonneg_right hCC (by positivity)
      _ ≤ C^2*(x+y)^2 := mul_le_mul_of_nonneg_left
        (by nlinarith only [mul_nonneg hx hy]) (sq_nonneg C)
      _ = _ := by ring
  exact (sq_le_sq₀ ht (mul_nonneg hC0 (add_nonneg hx hy))).mp (hs.trans hb)

/-- Balanced A-step for the actual two-power lower-derivative estimate.
No exponent-pair notion or derivative-test estimate is encoded in a class. -/
theorem weyl_vdC_norm_le_derivative_balance (f : ℤ → ℝ) (a : ℤ) (N : ℕ)
    {lam D alpha b : ℝ} (hN : 0 < N) (hlam : 0 < lam) (hD : 1 ≤ D)
    (ha : 0 < alpha) (ha1 : alpha < 1)
    (hX1 : 1 ≤ lam^(-(alpha/(alpha+1))))
    (hXN : lam^(-(alpha/(alpha+1))) ≤ (N:ℝ))
    (hshift : ∀ h : ℕ, 0 < h → h ≤ N →
      ‖∑ n ∈ (Finset.Ioc a (a+N)).filter (fun n => n+(h:ℤ) ∈ Finset.Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤
          D*((N:ℝ)*(lam*(h:ℝ))^alpha+(N:ℝ)^b*(lam*(h:ℝ))^(-alpha))) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (f n)‖ ≤
      (16*D/(1-alpha))*((N:ℝ)*lam^(alpha/(2*alpha+2))+
        (N:ℝ)^((b+1)/2)*lam^(-(alpha/(2*alpha+2)))) := by
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hden : 0 < 1-alpha := sub_pos.mpr ha1
  have haden : 0 < alpha+1 := by linarith only [ha]
  let beta : ℝ := alpha/(2*alpha+2)
  let X : ℝ := lam^(-(alpha/(alpha+1)))
  let x : ℝ := (N:ℝ)*lam^beta
  let y : ℝ := (N:ℝ)^((b+1)/2)*lam^(-beta)
  let K : ℝ := 16*D/(1-alpha)
  have hbeta : alpha/(alpha+1) = 2*beta := by
    dsimp only [beta]
    field_simp
  have hexp : alpha-alpha*(alpha/(alpha+1)) = 2*beta := by
    rw [← hbeta]
    field_simp
    ring
  have hpos : lam^alpha*X^alpha = lam^(2*beta) := by
    dsimp only [X]
    rw [← Real.rpow_mul hlam.le,← Real.rpow_add hlam]
    congr 1
    nlinarith only [hexp]
  have hneg : lam^(-alpha)*X^(-alpha) = lam^(-2*beta) := by
    dsimp only [X]
    rw [← Real.rpow_mul hlam.le,← Real.rpow_add hlam]
    congr 1
    nlinarith only [hexp]
  have hinv : 1/X = lam^(2*beta) := by
    dsimp only [X]
    rw [Real.rpow_neg hlam.le,one_div,inv_inv,hbeta]
  have hxsq : x^2 = (N:ℝ)^2*lam^(2*beta) := by
    dsimp only [x]
    rw [mul_pow,← Real.rpow_mul_natCast hlam.le beta 2]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  have hysq : y^2 = (N:ℝ)^(b+1)*lam^(-2*beta) := by
    dsimp only [y]
    rw [mul_pow,← Real.rpow_mul_natCast hNR.le ((b+1)/2) 2,
      ← Real.rpow_mul_natCast hlam.le (-beta) 2]
    norm_num only [Nat.cast_ofNat]
    congr 1 <;> congr 1 <;> ring
  have hNpow : (N:ℝ)^b*(N:ℝ) = (N:ℝ)^(b+1) := by
    rw [Real.rpow_add hNR,Real.rpow_one]
  have hb := weyl_vdC_sq_le_two_power_real_cutoff f a N
    (A := D*(N:ℝ)*lam^alpha) (B := D*(N:ℝ)^b*lam^(-alpha))
    (by positivity) (by positivity) ha ha1 hX1 hXN (fun h hh hhn => by
      apply (hshift h hh hhn).trans_eq
      simp only [Real.mul_rpow hlam.le (Nat.cast_nonneg h)]
      ring)
  have he1 : 4*(N:ℝ)^2/X = 4*x^2 := by rw [hxsq,div_eq_mul_one_div,hinv]; ring
  have he2 : 4*(N:ℝ)*(D*(N:ℝ)*lam^alpha)*X^alpha = 4*D*x^2 := by
    calc
      _ = 4*D*(N:ℝ)^2*(lam^alpha*X^alpha) := by ring
      _ = _ := by rw [hpos,hxsq]; ring
  have he3 : (8*(N:ℝ)*(D*(N:ℝ)^b*lam^(-alpha))/(1-alpha))*X^(-alpha) =
      (8*D/(1-alpha))*y^2 := by
    calc
      _ = (8*D/(1-alpha))*((N:ℝ)^b*(N:ℝ))*(lam^(-alpha)*X^(-alpha)) := by ring
      _ = _ := by rw [hNpow,hneg,hysq]; ring
  have hKlo : 16*D ≤ K := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [mul_nonneg hD0 ha.le]
  have hK1 : 1 ≤ K := by linarith only [hD,hKlo]
  have hcoef1 : 4+4*D ≤ K := by linarith only [hD,hKlo]
  have hcoef2 : 8*D/(1-alpha) ≤ K := by
    apply div_le_div_of_nonneg_right _ hden.le
    linarith only [hD0]
  have hs : ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (f n)‖^2 ≤ K*(x^2+y^2) := by
    change _ ≤ _ at hb
    rw [he1,he2,he3] at hb
    calc
      _ ≤ (4+4*D)*x^2+(8*D/(1-alpha))*y^2 := by nlinarith only [hb]
      _ ≤ K*x^2+K*y^2 := add_le_add
        (mul_le_mul_of_nonneg_right hcoef1 (sq_nonneg x))
        (mul_le_mul_of_nonneg_right hcoef2 (sq_nonneg y))
      _ = _ := by ring
  exact le_scaled_sum_of_sq_le (norm_nonneg _) (by positivity)
    (by positivity) hK1 hs

end WaveTurbulence.NumberTheory
