/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! # VINE-COUNT part 14: product inequalities for the ladder weights. -/
@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.VineCount

/-- Up to `2` missing factors of size `≤ Y`, the product of the weights to the powers `z` is bounded by the product
to the powers `c`. -/
theorem prod_pow_le_of_deficit {ι : Type*} (s : Finset ι) (X : ι → ℝ) (Y : ℝ) (z c b : ι → ℕ)
    (hX1 : ∀ i ∈ s, 1 ≤ X i) (hXY : ∀ i ∈ s, X i ≤ Y) (hY : 1 ≤ Y) (hzcb : ∀ i ∈ s, z i ≤ c i + b i)
    (hb : ∑ i ∈ s, b i ≤ 2) : ∏ i ∈ s, X i ^ z i ≤ Y ^ 2 * ∏ i ∈ s, X i ^ c i := by
  have h0 : ∀ i ∈ s, 0 ≤ X i := fun i hi => zero_le_one.trans (hX1 i hi)
  calc ∏ i ∈ s, X i ^ z i ≤ ∏ i ∈ s, (X i ^ c i * X i ^ b i) := by
        refine Finset.prod_le_prod₀ (fun i hi => pow_nonneg (h0 i hi) _) fun i hi => ?_
        rw [← pow_add]
        exact pow_le_pow_right₀ (hX1 i hi) (hzcb i hi)
    _ = (∏ i ∈ s, X i ^ c i) * ∏ i ∈ s, X i ^ b i := Finset.prod_mul_distrib
    _ ≤ (∏ i ∈ s, X i ^ c i) * ∏ i ∈ s, Y ^ b i := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i hi => pow_nonneg (h0 i hi) _)
          fun i hi => pow_le_pow_left₀ (h0 i hi) (hXY i hi) _) (Finset.prod_nonneg fun i hi => pow_nonneg (h0 i hi) _)
    _ = (∏ i ∈ s, X i ^ c i) * Y ^ (∑ i ∈ s, b i) := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ (∏ i ∈ s, X i ^ c i) * Y ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY hb) (Finset.prod_nonneg fun i hi => pow_nonneg (h0 i hi) _)
    _ = Y ^ 2 * ∏ i ∈ s, X i ^ c i := mul_comm _ _

/-- The product over the chart rungs of the weight of the ladder containing them. -/
theorem prod_fiber_weights {m : ℕ} {ι : Type*} [DecidableEq ι] (gl : Fin m → Option ι) (X : ι → ℝ) (T : Finset ι)
    (hT : ∀ j S, gl j = some S → S ∈ T) :
    ∏ j : Fin m, (gl j).elim 1 X = ∏ S ∈ T, X S ^ (Finset.univ.filter fun j => gl j = some S).card := by
  have h1 : ∀ j : Fin m, (gl j).elim 1 X = ∏ S ∈ T, (if gl j = some S then X S else 1) := by
    intro j
    cases hg : gl j with
    | none => simp
    | some S₀ =>
      have hS₀ : S₀ ∈ T := hT j S₀ hg
      rw [Finset.prod_eq_single S₀]
      · simp
      · intro S _ hne
        simp [Option.some.injEq, Ne.symm hne]
      · intro h; exact absurd hS₀ h
  simp_rw [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun S _ => ?_
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

end WaveTurbulence.VineCount
