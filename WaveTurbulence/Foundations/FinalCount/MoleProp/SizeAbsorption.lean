/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeNormalization
import Mathlib.Tactic

/-! # Absorbing component-size polynomial losses into the source exponential constant -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem nat_add_one_le_two_pow (n : ℕ) : (n : ℝ)+1 ≤ (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ,pow_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [ih,hn]

theorem size_polynomial_le_exponential (n m : ℕ) :
    ((n : ℝ)+1)^m ≤ ((2 : ℝ)^m)^n := by
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ)+1)
    (nat_add_one_le_two_pow n) m
  simpa only [← pow_mul,Nat.mul_comm] using h

theorem discarded_sizes_polynomial_le_exponential {I : Type*} (S : Finset I)
    (size : I → ℕ) (m : ℕ) :
    (∏ i ∈ S, ((size i : ℝ)+1)^m) ≤ ((2 : ℝ)^m)^(∑ i ∈ S, size i) := by
  calc
    _ ≤ ∏ i ∈ S, ((2 : ℝ)^m)^(size i) :=
      prod_le_prod₀ (fun i _ => by positivity) (fun i _ => size_polynomial_le_exponential (size i) m)
    _ = _ := prod_pow_eq_pow_sum S size ((2 : ℝ)^m)

end WaveTurbulence.MoleProp
