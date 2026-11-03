/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Joint frequency decay from finitely many Fourier moments

Controlling all square-free products of a finite collection of frequencies
gives a product of inverse Japanese brackets. This is the elementary
algebra used after integration by parts in DNY21 Lemma 3.1 and TARGET A.3.
-/

public section

namespace WaveTurbulence.Fourier

/-- The Japanese bracket is bounded by one plus absolute value. -/
theorem japaneseBracket_le_one_add_abs (x : ℝ) :
    Real.sqrt (1 + x ^ 2) ≤ 1 + |x| := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (1 + x ^ 2)
  nlinarith [sq_abs x, abs_nonneg x]

/-- A square-free moment bound for every subset gives joint Japanese-bracket decay.
This is an algebraic helper; the Fourier moment bounds are proved for each operator separately. -/
theorem frequency_decay_of_moments {ι : Type*} [Fintype ι]
    (z : ℂ) (ξ : ι → ℝ) (C : ℝ)
    (h : ∀ s : Finset ι, (∏ i ∈ s, |ξ i|) * ‖z‖ ≤ C) :
    ‖z‖ ≤ (2 : ℝ) ^ Fintype.card ι * C / (∏ i, Real.sqrt (1 + ξ i ^ 2)) := by
  classical
  have hp : 0 < ∏ i, Real.sqrt (1 + ξ i ^ 2) :=
    Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (by positivity)
  apply (le_div_iff₀ hp).mpr
  have hprod : (∏ i, Real.sqrt (1 + ξ i ^ 2)) ≤ ∏ i, (1 + |ξ i|) :=
    Finset.prod_le_prod₀ (fun i _ => Real.sqrt_nonneg _) (fun i _ => japaneseBracket_le_one_add_abs _)
  calc
    ‖z‖ * (∏ i, Real.sqrt (1 + ξ i ^ 2)) ≤ ‖z‖ * (∏ i, (1 + |ξ i|)) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ∑ s ∈ (Finset.univ : Finset ι).powerset, ‖z‖ * ∏ i ∈ s, |ξ i| := by
      rw [Finset.prod_one_add, Finset.mul_sum]
    _ ≤ ∑ _s ∈ (Finset.univ : Finset ι).powerset, C := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [mul_comm] using h s
    _ = _ := by simp

/-- Two-frequency specialization, with separate moment hypotheses for convenient use. -/
theorem frequency_decay_two (z : ℂ) (x y C : ℝ)
    (h0 : ‖z‖ ≤ C) (hx : |x| * ‖z‖ ≤ C) (hy : |y| * ‖z‖ ≤ C)
    (hxy : (|x| * |y|) * ‖z‖ ≤ C) :
    ‖z‖ ≤ 4 * C / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) := by
  have hp : 0 < Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) := by positivity
  apply (le_div_iff₀ hp).mpr
  have hb := mul_le_mul (japaneseBracket_le_one_add_abs x)
    (japaneseBracket_le_one_add_abs y) (Real.sqrt_nonneg _) (by positivity : 0 ≤ 1 + |x|)
  have hz := mul_le_mul_of_nonneg_left hb (norm_nonneg z)
  nlinarith

end WaveTurbulence.Fourier
