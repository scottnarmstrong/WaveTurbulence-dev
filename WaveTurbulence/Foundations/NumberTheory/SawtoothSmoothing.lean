/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.Sawtooth
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-!
# Continuous one-sided envelopes for the sawtooth

For the circle problem, the unsummed pointwise Fourier error does not by itself
give the required power saving. Differences of the continuous periodic second
Bernoulli polynomial give one-sided envelopes with absolutely convergent
Fourier series. These statements retain the sawtooth value at every integer.
This is an ingredient towards NT-CIRCLE-v2 goal 2, not a circle estimate.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The continuous periodization of the second Bernoulli polynomial. -/
@[expose] noncomputable def periodicBernoulliTwo (x : ℝ) : ℝ :=
  Int.fract x ^ 2 - Int.fract x + 1 / 6

private theorem bernoulli_forward_algebra {t v h k : ℝ}
    (ht : 0 ≤ v) (hk : k = 0 ∨ 1 ≤ k) (hrel : v = t + h - k) :
    (v ^ 2 - v + 1 / 6) - (t ^ 2 - t + 1 / 6) ≤
      2 * h * (t - 1 / 2) + h ^ 2 := by
  have hh : h = v - t + k := by linarith only [hrel]
  rw [hh]
  rcases hk with rfl | hk
  · ring_nf
    exact le_rfl
  · have hp : 0 ≤ k * (k - 1 + 2 * v) :=
      mul_nonneg (zero_le_one.trans hk) (by linarith only [hk, ht])
    nlinarith only [hp]

private theorem bernoulli_backward_algebra {t v h k : ℝ}
    (hv : v ≤ 1) (hk : k = 0 ∨ 1 ≤ k) (hrel : h = t - v + k) :
    2 * h * (t - 1 / 2) - h ^ 2 ≤
      (t ^ 2 - t + 1 / 6) - (v ^ 2 - v + 1 / 6) := by
  rw [hrel]
  rcases hk with rfl | hk
  · ring_nf
    exact le_rfl
  · have hp : 0 ≤ k * (k + 1 - 2 * v) :=
      mul_nonneg (zero_le_one.trans hk) (by linarith only [hk, hv])
    nlinarith only [hp]

/-- A continuous lower envelope, valid at integer inputs as well. -/
theorem periodicBernoulliTwo_sub_le {x h : ℝ} (hh : 0 ≤ h) :
    periodicBernoulliTwo (x + h) - periodicBernoulliTwo x ≤
      2 * h * sawtooth x + h ^ 2 := by
  let k : ℤ := ⌊x + h⌋ - ⌊x⌋
  have hk : 0 ≤ k := sub_nonneg.mpr (Int.floor_mono (le_add_of_nonneg_right hh))
  have hk' : (k : ℝ) = 0 ∨ 1 ≤ (k : ℝ) := by
    rcases eq_or_lt_of_le hk with heq | hlt
    · left
      exact_mod_cast heq.symm
    · right
      exact_mod_cast hlt
  have hrel : Int.fract (x + h) = Int.fract x + h - (k : ℝ) := by
    dsimp only [k, Int.fract]
    push_cast
    ring
  exact bernoulli_forward_algebra (Int.fract_nonneg _) hk' hrel

/-- The matching upper envelope. -/
theorem le_periodicBernoulliTwo_sub {x h : ℝ} (hh : 0 ≤ h) :
    2 * h * sawtooth x - h ^ 2 ≤
      periodicBernoulliTwo x - periodicBernoulliTwo (x - h) := by
  let k : ℤ := ⌊x⌋ - ⌊x - h⌋
  have hk : 0 ≤ k := sub_nonneg.mpr (Int.floor_mono (sub_le_self x hh))
  have hrel : h = Int.fract x - Int.fract (x - h) + (k : ℝ) := by
    dsimp only [k, Int.fract]
    push_cast
    ring
  have hk' : (k : ℝ) = 0 ∨ 1 ≤ (k : ℝ) := by
    rcases eq_or_lt_of_le hk with heq | hlt
    · left
      exact_mod_cast heq.symm
    · right
      exact_mod_cast hlt
  exact bernoulli_backward_algebra (Int.fract_lt_one _).le hk' hrel

/-- The forward difference of `B₂`, with mean `-h/2`, minorizes the sawtooth. -/
theorem sawtooth_lower_envelope {x h : ℝ} (hh : 0 < h) :
    (periodicBernoulliTwo (x + h) - periodicBernoulliTwo x) / (2 * h) - h / 2 ≤
      sawtooth x := by
  have h := periodicBernoulliTwo_sub_le (x := x) hh.le
  rw [sub_le_iff_le_add, div_le_iff₀ (mul_pos zero_lt_two hh)]
  nlinarith only [h]

/-- The backward difference of `B₂`, with mean `h/2`, majorizes the sawtooth. -/
theorem sawtooth_upper_envelope {x h : ℝ} (hh : 0 < h) :
    sawtooth x ≤
      (periodicBernoulliTwo x - periodicBernoulliTwo (x - h)) / (2 * h) + h / 2 := by
  have h := le_periodicBernoulliTwo_sub (x := x) hh.le
  rw [← sub_le_iff_le_add, le_div_iff₀ (mul_pos zero_lt_two hh)]
  nlinarith only [h]

private theorem bernoulli_two_eval (x : ℝ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)).eval x =
      x ^ 2 - x + 1 / 6 := by
  norm_num [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_zero,
    bernoulli_one, bernoulli_two, Polynomial.map_monomial, Polynomial.eval_monomial]
  ring

private theorem cos_nat_mul_fract (x : ℝ) (n : ℕ) :
    Real.cos (2 * Real.pi * (n : ℝ) * Int.fract x) =
      Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  rw [show 2 * Real.pi * (n : ℝ) * Int.fract x =
      2 * Real.pi * (n : ℝ) * x + ((-(n : ℤ) * ⌊x⌋ : ℤ) : ℝ) * (2 * Real.pi) by
    dsimp only [Int.fract]
    push_cast
    ring]
  exact Real.cos_add_int_mul_two_pi _ _

/-- The absolutely convergent Fourier series of the smoothing primitive.
It holds at every real input, including integers; the zero summand is zero. -/
theorem hasSum_periodicBernoulliTwo (x : ℝ) :
    HasSum (fun n : ℕ => Real.cos (2 * Real.pi * (n : ℝ) * x) / (n : ℝ) ^ 2)
      (Real.pi ^ 2 * periodicBernoulliTwo x) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) (by decide)
    (x := Int.fract x) ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  norm_num only [Nat.mul_one, Nat.reduceAdd, pow_two, neg_one_sq,
    one_mul, Nat.factorial_two, Nat.cast_ofNat, bernoulli_two_eval] at h
  convert h using 1
  · funext n
    rw [cos_nat_mul_fract]
    ring
  · dsimp only [periodicBernoulliTwo]
    ring

end WaveTurbulence.NumberTheory
