/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact bandwidth identities for the full-star estimate -/

public section
namespace WaveTurbulence.CountLemmas

theorem star_nn_monomial {L τ : ℝ} (hL : 0 < L) (hτ : τ ≠ 0) (A ε : ℝ) :
    τ^2*L^A*L^(2*ε)*(1/(4*τ*L^2))^2 = L^(A+2*ε-4)/16 := by
  rw [Real.rpow_sub hL,Real.rpow_add hL,show L^(4 : ℝ) = L^4 by norm_cast]
  field_simp
  ring

theorem star_nz_monomial {L τ : ℝ} (hL : 0 < L) (hτ : τ ≠ 0) (A ε : ℝ) :
    τ^2*L^A*L^(-1+4*ε)*(1/(4*τ*L^2)) = τ*L^(A-3+4*ε)/4 := by
  have heq : L^(A-3+4*ε) = L^A*L^(-1+4*ε)/L^2 := by
    calc
      _ = L^((A+(-1+4*ε))-2) := by congr 1; ring
      _ = L^(A+(-1+4*ε))/L^(2 : ℝ) := Real.rpow_sub hL _ _
      _ = _ := by rw [Real.rpow_two]; exact congrArg (fun t : ℝ => t/L^2) (Real.rpow_add hL A (-1+4*ε))
  rw [heq]
  field_simp

theorem bandwidth_mul_rpow {L : ℝ} (hL : 0 < L) (δ γ a : ℝ) :
    (δ⁻¹*L^(-2*γ))*L^a = δ⁻¹*L^(a-2*γ) := by
  rw [mul_assoc,← Real.rpow_add hL]
  congr 2
  ring

theorem bandwidth_sq_mul_rpow {L : ℝ} (hL : 0 < L) (δ γ a : ℝ) :
    (δ⁻¹*L^(-2*γ))^2*L^a = δ⁻¹^2*L^(a-4*γ) := by
  rw [mul_pow,← Real.rpow_mul_natCast hL.le,mul_assoc,← Real.rpow_add hL]
  congr 2
  norm_num
  ring

end WaveTurbulence.CountLemmas
