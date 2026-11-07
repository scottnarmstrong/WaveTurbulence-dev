/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact monomial identities for the actual K4 energy tolerance

These formulas insert τ=D L^(−2γ) into the three retained radial terms.
They are algebraic identities, not asymptotic or counting hypotheses.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem k4_tau_square_monomial (n : ℕ) {L D γ e : ℝ} (hL : 0 < L) :
    D*L^n*L^e*((D*L^(-2*γ))^2*L^3) = D^3*L^((n : ℝ)+e+3-4*γ) := by
  have ht : (L^(-2*γ))^2=L^(-4*γ) := by
    rw [← Real.rpow_mul_natCast hL.le]
    congr 1
    ring
  have hthree : L^(3 : ℝ)=L^(3 : ℕ) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast L 3
  rw [mul_pow,ht]
  calc
    _ = D^3*(L^(n : ℝ)*L^e*L^(-4*γ)*L^(3 : ℝ)) := by simp only [Real.rpow_natCast,hthree]; ring
    _ = _ := by rw [← Real.rpow_add hL,← Real.rpow_add hL,← Real.rpow_add hL]; congr 2; ring

theorem k4_tau_linear_monomial (n : ℕ) {L D γ e : ℝ} (hL : 0 < L) :
    D*L^n*L^e*((D*L^(-2*γ))*L^2) = D^2*L^((n : ℝ)+e+2-2*γ) := by
  calc
    _ = D^2*(L^(n : ℝ)*L^e*L^(-2*γ)*L^(2 : ℝ)) := by simp only [Real.rpow_natCast,Real.rpow_two]; ring
    _ = _ := by rw [← Real.rpow_add hL,← Real.rpow_add hL,← Real.rpow_add hL]; congr 2; ring

theorem k4_tau_zero_monomial (n : ℕ) {L D e : ℝ} (hL : 0 < L) :
    D*L^n*L^e*L = D*L^((n : ℝ)+e+1) := by
  calc
    _ = D*(L^(n : ℝ)*L^e*L^(1 : ℝ)) := by simp only [Real.rpow_natCast,Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hL,← Real.rpow_add hL]

end WaveTurbulence.MoleProp
