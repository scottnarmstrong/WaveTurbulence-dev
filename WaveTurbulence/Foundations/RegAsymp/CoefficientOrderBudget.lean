/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.OrderLoss
import Mathlib.Tactic

/-! # Absorbing the literal J3 coefficient masses into geometric order constants

For a couple of half-order n, J3 supplies C₀^(4n+1). The auxiliary
positive-envelope masses and the number of active variables remain geometric.
-/

public section
namespace WaveTurbulence.RegAsymp

/-- Fixed coefficient masses and a linear variable count fit one geometric
constant, for every positive half-order. -/
theorem coefficient_mass_le_geometric {n : ℕ} (hn : 0 < n) {u v C : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hC : 1 ≤ C) :
    ((n:ℝ)+2*u)*C^(4*n+1)+v ≤ (3*(1+2*u+v)*C^5)^n := by
  let H := 1+2*u+v
  have hH : 1 ≤ H := by dsimp only [H]; linarith
  have hN : 1 ≤ C^(4*n+1) := one_le_pow₀ hC
  have hN' : C^(4*n+1) ≤ (C^5)^n := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hC (by omega)
  have hpoly : 2*(n:ℝ)+1 ≤ (3:ℝ)^n := by
    simpa only [pow_one] using leaf_polynomial_le_geometric n 1
  have hHpow : H ≤ H^n := le_self_pow₀ hH hn.ne'
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hlin : (n:ℝ)+2*u+v ≤ (2*(n:ℝ)+1)*H := by
    have hprod : 0 ≤ (2*(n:ℝ))*((2*u)+v) := mul_nonneg (by positivity) (by positivity)
    dsimp only [H]
    nlinarith only [hprod,hn0]
  calc
    _ ≤ ((n:ℝ)+2*u+v)*C^(4*n+1) := by
      have hh := mul_le_mul_of_nonneg_left hN hv
      nlinarith only [hh]
    _ ≤ ((2*(n:ℝ)+1)*H)*C^(4*n+1) :=
      mul_le_mul_of_nonneg_right hlin (by positivity)
    _ ≤ ((3:ℝ)^n*H^n)*(C^5)^n :=
      mul_le_mul (mul_le_mul hpoly hHpow (by positivity) (by positivity)) hN'
        (by positivity) (by positivity)
    _ = _ := by rw [← mul_pow,← mul_pow]

end WaveTurbulence.RegAsymp
