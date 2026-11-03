/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.SawtoothSmoothing
public import WaveTurbulence.Foundations.NumberTheory.Phase
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Fourier bounds for one-sided sawtooth smoothing

An ingredient towards NT-CIRCLE-v2 goal 2. The Fourier majorant is summable
without any assumption on the phase values. No exponential-sum estimate or
circle discrepancy estimate is included as a hypothesis.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- A finite exponential sum is bounded by its number of terms. -/
theorem norm_sum_expPhase_le_card {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ‖∑ i ∈ s, expPhase (f i)‖ ≤ s.card := by
  calc
    _ ≤ ∑ i ∈ s, ‖expPhase (f i)‖ := norm_sum_le s _
    _ = s.card := by simp only [norm_expPhase, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The chord of a unit complex phase has length at most two. -/
theorem norm_expPhase_sub_one_le_two (x : ℝ) : ‖expPhase x - 1‖ ≤ 2 := by
  calc
    _ ≤ ‖expPhase x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_expPhase, norm_one]; norm_num

/-- The same chord has the linear bound needed at low frequencies. -/
theorem norm_expPhase_sub_one_le (x : ℝ) : ‖expPhase x - 1‖ ≤ 2 * Real.pi * |x| := by
  rw [norm_sub_rev, norm_one_sub_expPhase]
  have h : |Real.sin (Real.pi * x)| ≤ |Real.pi * x| := Real.abs_sin_le_abs
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  linarith only [h]

/-- Summability of the exact smoothing Fourier majorant, even before using
any cancellation in the finite exponential sums. -/
theorem summable_smoothing_majorant {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ℝ) :
    Summable (fun n : ℕ =>
      ‖expPhase ((n : ℝ) * h) - 1‖ * ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ /
        (n : ℝ) ^ 2) := by
  have hsum : Summable (fun n : ℕ => (2 * (s.card : ℝ)) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left _
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsum
  intro n
  have hprod := mul_le_mul
    (norm_expPhase_sub_one_le_two ((n : ℝ) * h))
    (norm_sum_expPhase_le_card s (fun i => (n : ℝ) * f i))
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [div_eq_mul_inv, one_mul] using
    div_le_div_of_nonneg_right hprod (sq_nonneg (n : ℝ))

private theorem cos_diff_sum_eq_re {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ℝ) (n : ℕ) :
    (∑ i ∈ s, (Real.cos (2 * Real.pi * (n : ℝ) * (f i + h)) -
        Real.cos (2 * Real.pi * (n : ℝ) * f i)) / (n : ℝ) ^ 2) =
      ((expPhase ((n : ℝ) * h) - 1) *
        ∑ i ∈ s, expPhase ((n : ℝ) * f i)).re / (n : ℝ) ^ 2 := by
  have hre (x : ℝ) : Real.cos (2 * Real.pi * (n : ℝ) * x) =
      (expPhase ((n : ℝ) * x)).re := by
    rw [expPhase_re]
    congr 1
    ring
  simp_rw [hre]
  rw [← Finset.sum_div, Finset.mul_sum, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [sub_mul, one_mul, ← expPhase_add, Complex.sub_re]
  rw [show (n : ℝ) * h + (n : ℝ) * f i = (n : ℝ) * (f i + h) by ring]

/-- The sum of differences of the periodic Bernoulli primitive is bounded
by the exact absolutely convergent Fourier majorant. -/
theorem abs_sum_periodicBernoulliTwo_diff_le {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (h : ℝ) :
    |Real.pi ^ 2 * ∑ i ∈ s, (periodicBernoulliTwo (f i + h) - periodicBernoulliTwo (f i))| ≤
      ∑' n : ℕ, ‖expPhase ((n : ℝ) * h) - 1‖ *
        ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ / (n : ℝ) ^ 2 := by
  have hB := hasSum_sum (s := s) (fun i _ =>
    (hasSum_periodicBernoulliTwo (f i + h)).sub (hasSum_periodicBernoulliTwo (f i)))
  have hseries : HasSum (fun n : ℕ => ∑ i ∈ s,
      (Real.cos (2 * Real.pi * (n : ℝ) * (f i + h)) -
        Real.cos (2 * Real.pi * (n : ℝ) * f i)) / (n : ℝ) ^ 2)
      (Real.pi ^ 2 * ∑ i ∈ s, (periodicBernoulliTwo (f i + h) - periodicBernoulliTwo (f i))) := by
    convert hB using 1
    · funext n
      apply Finset.sum_congr rfl
      intro i _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  have h := hseries.norm_le_of_bounded (summable_smoothing_majorant s f h).hasSum
    (fun n => ?_)
  · simpa only [Real.norm_eq_abs] using h
  rw [cos_diff_sum_eq_re]
  simp only [norm_div, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
  exact (Complex.abs_re_le_norm _).trans_eq (norm_mul _ _)

private theorem norm_expPhase_neg_sub_one (x : ℝ) :
    ‖expPhase (-x) - 1‖ = ‖expPhase x - 1‖ := by
  calc
    _ = ‖(starRingEnd ℂ) (expPhase x - 1)‖ := by
      rw [map_sub, map_one, conj_expPhase]
    _ = _ := Complex.norm_conj _

/-- The two one-sided continuous envelopes give a Fourier bound for an
arbitrary finite sawtooth sum. The infinite series is unconditionally summable
by `summable_smoothing_majorant`; its chord factor supplies the high-frequency
decay needed by the circle-problem application. -/
theorem abs_sum_sawtooth_le_smoothing_series {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) {h : ℝ} (hh : 0 < h) :
    |∑ i ∈ s, sawtooth (f i)| ≤ (s.card : ℝ) * (h / 2) +
      (∑' n : ℕ, ‖expPhase ((n : ℝ) * h) - 1‖ *
        ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ / (n : ℝ) ^ 2) /
        (2 * h * Real.pi ^ 2) := by
  let D := ∑' n : ℕ, ‖expPhase ((n : ℝ) * h) - 1‖ *
    ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ / (n : ℝ) ^ 2
  have hplus := abs_sum_periodicBernoulliTwo_diff_le s f h
  change |Real.pi ^ 2 * ∑ i ∈ s,
    (periodicBernoulliTwo (f i + h) - periodicBernoulliTwo (f i))| ≤ D at hplus
  have hminus := abs_sum_periodicBernoulliTwo_diff_le s f (-h)
  have hneg : (∑' n : ℕ, ‖expPhase ((n : ℝ) * -h) - 1‖ *
      ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ / (n : ℝ) ^ 2) = D := by
    apply tsum_congr
    intro n
    rw [mul_neg, norm_expPhase_neg_sub_one]
  rw [hneg] at hminus
  have hlow := Finset.sum_le_sum (s := s) (fun i _ => sawtooth_lower_envelope (x := f i) hh)
  have hupp := Finset.sum_le_sum (s := s) (fun i _ => sawtooth_upper_envelope (x := f i) hh)
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul] at hlow
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul] at hupp
  have hppos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have h2pos : 0 < 2 * h := mul_pos zero_lt_two hh
  have hplus' : -D / Real.pi ^ 2 ≤
      ∑ i ∈ s, (periodicBernoulliTwo (f i + h) - periodicBernoulliTwo (f i)) := by
    rw [div_le_iff₀ hppos]
    have hl := (abs_le.mp hplus).1
    linarith only [hl]
  have hminus' : (∑ i ∈ s, (periodicBernoulliTwo (f i) - periodicBernoulliTwo (f i - h))) ≤
      D / Real.pi ^ 2 := by
    rw [le_div_iff₀ hppos]
    have hl := (abs_le.mp hminus).1
    have heq : (∑ i ∈ s, (periodicBernoulliTwo (f i) - periodicBernoulliTwo (f i - h))) =
        -(∑ i ∈ s, (periodicBernoulliTwo (f i + -h) - periodicBernoulliTwo (f i))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
    rw [heq]
    linarith only [hl]
  have hl := div_le_div_of_nonneg_right hplus' h2pos.le
  have hu := div_le_div_of_nonneg_right hminus' h2pos.le
  have hdiv : D / Real.pi ^ 2 / (2 * h) = D / (2 * h * Real.pi ^ 2) := by ring
  have hnegdiv : -D / Real.pi ^ 2 / (2 * h) = -(D / (2 * h * Real.pi ^ 2)) := by ring
  rw [hdiv] at hu
  rw [hnegdiv] at hl
  exact abs_le.mpr ⟨by linarith only [hlow, hl], by linarith only [hupp, hu]⟩

end WaveTurbulence.NumberTheory
