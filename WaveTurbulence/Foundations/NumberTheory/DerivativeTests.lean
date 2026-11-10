/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.SecondDifference
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
# From derivatives to discrete exponential sums

NT-CIRCLE-v2 goal 1. Mean value theorems discharge the discrete hypotheses
of Kusmin–Landau and the second-difference test from bounds on actual real
derivatives. All derivatives and bounds are needed only on the indicated
closed real interval, including the extra endpoint used by the discrete sum.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Reversing a real phase conjugates its sum and preserves its norm. -/
theorem norm_sum_expPhase_neg {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ‖∑ i ∈ s, expPhase (-f i)‖ = ‖∑ i ∈ s, expPhase (f i)‖ := by
  simp_rw [← conj_expPhase]
  rw [← map_sum, Complex.norm_conj]

/-- The unit-interval mean value theorem, keeping the location of the witness. -/
theorem exists_unit_increment_eq {f f' : ℝ → ℝ} {x : ℝ}
    (hf : ∀ y ∈ Set.Icc x (x + 1), HasDerivAt f (f' y) y) :
    ∃ y ∈ Set.Ioo x (x + 1), f' y = f (x + 1) - f x := by
  have hcont : ContinuousOn f (Set.Icc x (x + 1)) :=
    fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hlt : x < x + 1 := lt_add_one x
  obtain ⟨y, hy, heq⟩ := exists_hasDerivAt_eq_slope f f' hlt hcont
    (fun z hz => hf z (Set.Ioo_subset_Icc_self hz))
  refine ⟨y, hy, ?_⟩
  simpa only [add_sub_cancel_left, div_one] using heq

/-- Bounds on a real derivative give bounds on its unit increment. -/
theorem unit_increment_mem_Icc {f f' : ℝ → ℝ} {x l u : ℝ}
    (hf : ∀ y ∈ Set.Icc x (x + 1), HasDerivAt f (f' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + 1), f' y ∈ Set.Icc l u) :
    f (x + 1) - f x ∈ Set.Icc l u := by
  obtain ⟨y, hy, heq⟩ := exists_unit_increment_eq hf
  rw [← heq]
  exact hbound y (Set.Ioo_subset_Icc_self hy)

/-- Two successive mean value theorems transfer bounds on the second
derivative to second unit differences, on exactly the required interval. -/
theorem second_increment_mem_Icc {f f' f'' : ℝ → ℝ} {x l u : ℝ}
    (hf : ∀ y ∈ Set.Icc x (x + 2), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + 2), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + 2), f'' y ∈ Set.Icc l u) :
    (f (x + 1 + 1) - f (x + 1)) - (f (x + 1) - f x) ∈ Set.Icc l u := by
  have hsub {y : ℝ} (hy : y ∈ Set.Icc x (x + 1)) :
      Set.Icc y (y + 1) ⊆ Set.Icc x (x + 2) := by
    intro z hz
    constructor <;> linarith only [hy.1, hy.2, hz.1, hz.2]
  apply unit_increment_mem_Icc
    (f' := fun y => f' (y + 1) - f' y)
    (f := fun y => f (y + 1) - f y)
  · intro y hy
    have hy0 : y ∈ Set.Icc x (x + 2) := hsub hy ⟨le_rfl, (lt_add_one y).le⟩
    have hy1 : y + 1 ∈ Set.Icc x (x + 2) :=
      hsub hy ⟨(lt_add_one y).le, le_rfl⟩
    exact ((hf (y + 1) hy1).comp_add_const y 1).sub (hf y hy0)
  · intro y hy
    exact unit_increment_mem_Icc (fun z hz => hf' z (hsub hy hz))
      (fun z hz => hbound z (hsub hy hz))

/-- Van der Corput's second-derivative test, with explicit absolute constant
eight and derivative ratio `c`. The real phase and both derivatives are
required only on `[a+1,b+1]`; the sum is over integers in `(a,b]`. -/
theorem van_der_corput_second_derivative {f f' f'' : ℝ → ℝ} {a b : ℕ} {lam c : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hc : 1 ≤ c)
    (hf : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1), HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1),
      f'' x ∈ Set.Icc lam (c * lam)) :
    ‖∑ n ∈ Finset.Ioc a b, expPhase (f n)‖ ≤
      8 * (c * ((b : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  have hdiff (n : ℕ) (han : a < n) (hnb : n < b) :
      (f ((n : ℝ) + 1 + 1) - f ((n : ℝ) + 1)) -
        (f ((n : ℝ) + 1) - f n) ∈ Set.Icc lam (c * lam) := by
    have hsub : Set.Icc (n : ℝ) ((n : ℝ) + 2) ⊆
        Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1) := by
      have ha : (a : ℝ) + 1 ≤ n := by exact_mod_cast han
      have hb : (n : ℝ) + 1 ≤ b := by exact_mod_cast hnb
      intro x hx
      constructor <;> linarith only [ha, hb, hx.1, hx.2]
    exact second_increment_mem_Icc (fun x hx => hf x (hsub hx))
      (fun x hx => hf' x (hsub hx)) (fun x hx => hbound x (hsub hx))
  apply van_der_corput_second_difference hab hlam hc
  · intro n han hnb
    simpa only [Nat.cast_add, Nat.cast_one] using (hdiff n han hnb).1
  · intro n han hnb
    simpa only [Nat.cast_add, Nat.cast_one] using (hdiff n han hnb).2

/-- The second-derivative test for a negative second derivative, with the
same constant as the positive case. -/
theorem van_der_corput_second_derivative_of_neg {f f' f'' : ℝ → ℝ}
    {a b : ℕ} {lam c : ℝ} (hab : a ≤ b) (hlam : 0 < lam) (hc : 1 ≤ c)
    (hf : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1), HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1),
      f'' x ∈ Set.Icc (-(c * lam)) (-lam)) :
    ‖∑ n ∈ Finset.Ioc a b, expPhase (f n)‖ ≤
      8 * (c * ((b : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  rw [← norm_sum_expPhase_neg]
  apply van_der_corput_second_derivative (f := fun x => -f x) (f' := fun x => -f' x)
    (f'' := fun x => -f'' x) hab hlam hc
  · intro x hx
    exact (hf x hx).neg
  · intro x hx
    exact (hf' x hx).neg
  · intro x hx
    obtain ⟨hl, hu⟩ := hbound x hx
    constructor <;> linarith only [hl, hu]

end WaveTurbulence.NumberTheory
