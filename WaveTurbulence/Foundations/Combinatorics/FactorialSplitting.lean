/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Combinatorics.BinomialConvolution
public import WaveTurbulence.Foundations.Combinatorics.MultiVandermonde

/-!
# Factorial splitting estimates

DH21 Lemma A.4 (`combineq`, L2814–L2822), in iterated-binomial form.
Each step selects the next multi-index and leaves the coordinatewise remainder.
The product of binomial coefficients telescopes to the source multinomial
coefficient. `factorialSplitSum n` has `n+1` groups, so nine groups use `n = 8`.
The bound is uniform in the number of coordinates.
-/

public section

namespace WaveTurbulence.Combinatorics
open Finset
open scoped Classical

/-- The two-group multi-index factorial convolution has constant four. -/
theorem sum_multi_choose_factorial_le {ι : Type*} [Fintype ι] (ρ : ι → ℕ) :
    ∑ b : (∀ i, Fin (ρ i + 1)), (∏ i, ((ρ i).choose (b i) : ℝ)) *
      (2 * ∑ i, (b i : ℕ)).factorial *
      (2 * ∑ i, (ρ i - (b i : ℕ))).factorial ≤
      4 * (2 * ∑ i, ρ i).factorial := by
  have heq := sum_multi_choose_weight ρ
    (fun B => ((2 * B).factorial : ℝ) * (2 * ((∑ i, ρ i) - B)).factorial)
  have hsum (b : ∀ i, Fin (ρ i + 1)) :
      (∑ i, (ρ i - (b i : ℕ))) = (∑ i, ρ i) - ∑ i, (b i : ℕ) :=
    sum_tsub_distrib univ (fun j _ => Nat.le_of_lt_succ (b j).isLt)
  simp only [← hsum, ← mul_assoc] at heq
  rw [heq]
  exact sum_choose_factorial_le _

/-- Iterated multinomial factorial sum with `n+1` groups. Splitting off one
multi-index at a time counts each decomposition once. -/
@[expose] noncomputable def factorialSplitSum {ι : Type*} [Fintype ι] :
    ℕ → (ι → ℕ) → ℝ
  | 0, ρ => (2 * ∑ i, ρ i).factorial
  | n + 1, ρ => ∑ b : (∀ i, Fin (ρ i + 1)),
      (∏ i, ((ρ i).choose (b i) : ℝ)) *
      (2 * ∑ i, (b i : ℕ)).factorial *
      factorialSplitSum n (fun i => ρ i - (b i : ℕ))

/-- DH21 Lemma A.4 for any positive number of groups, with explicit constant. -/
theorem factorialSplitSum_le {ι : Type*} [Fintype ι] (n : ℕ) (ρ : ι → ℕ) :
    factorialSplitSum n ρ ≤ 4 ^ n * (2 * ∑ i, ρ i).factorial := by
  induction n generalizing ρ with
  | zero => simp [factorialSplitSum]
  | succ n ih =>
    calc
      _ ≤ ∑ b : (∀ i, Fin (ρ i + 1)),
          (∏ i, ((ρ i).choose (b i) : ℝ)) *
          (2 * ∑ i, (b i : ℕ)).factorial *
          (4 ^ n * (2 * ∑ i, (ρ i - (b i : ℕ))).factorial) := by
        apply sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (ih _) (by positivity)
      _ = 4 ^ n * (∑ b : (∀ i, Fin (ρ i + 1)),
          (∏ i, ((ρ i).choose (b i) : ℝ)) *
          (2 * ∑ i, (b i : ℕ)).factorial *
          (2 * ∑ i, (ρ i - (b i : ℕ))).factorial) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro b _
        ring
      _ ≤ 4 ^ n * (4 * (2 * ∑ i, ρ i).factorial) :=
        mul_le_mul_of_nonneg_left (sum_multi_choose_factorial_le ρ) (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- The nine-group instance used in DH21 Lemma A.4. -/
theorem factorialSplitSum_nine_le {ι : Type*} [Fintype ι] (ρ : ι → ℕ) :
    factorialSplitSum 8 ρ ≤ 65536 * (2 * ∑ i, ρ i).factorial := by
  convert factorialSplitSum_le 8 ρ using 1
  norm_num

end WaveTurbulence.Combinatorics
