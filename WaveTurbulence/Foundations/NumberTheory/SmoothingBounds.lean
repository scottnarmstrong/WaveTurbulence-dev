/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.SmoothingFourier
public import WaveTurbulence.Foundations.NumberTheory.HalfPowerSums
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Quantitative Fourier smoothing under a square-root frequency bound

A reusable conditional Fourier inequality towards NT-CIRCLE-v2 goal 2.
The frequency estimate is explicitly a premise of this inequality; it is
not asserted to hold for arbitrary phases or substituted for the circle
problem. Circle applications must discharge it from the actual arc geometry.
-/

public section

namespace WaveTurbulence.NumberTheory

private theorem low_sqrt_weight {n t C : ℝ} (hn : n ≠ 0) (ht : t ≠ 0)
    (heq : t ^ 2 = n) : C * n * t / n ^ 2 = C / t := by
  apply (div_eq_div_iff (pow_ne_zero 2 hn) ht).mpr
  calc
    C * n * t * t = C * n * t ^ 2 := by ring
    _ = C * n ^ 2 := by rw [heq]; ring

private theorem high_sqrt_weight {n t C : ℝ} (hn : n ≠ 0) (ht : t ≠ 0)
    (heq : t ^ 2 = n) : C * t / n ^ 2 = C / (n * t) := by
  apply (div_eq_div_iff (pow_ne_zero 2 hn) (mul_ne_zero hn ht)).mpr
  calc
    C * t * (n * t) = C * n * t ^ 2 := by ring
    _ = C * n ^ 2 := by rw [heq]; ring

private theorem smoothing_term_le_low {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {A : ℝ} {H n : ℕ} (hH : 0 < H) (hn : 0 < n)
    (hbound : ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ ≤ A * Real.sqrt n) :
    ‖expPhase ((n : ℝ) * (1 / H)) - 1‖ *
        ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ / (n : ℝ) ^ 2 ≤
      (2 * Real.pi * A / H) * (1 / Real.sqrt n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  have ht : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hc := norm_expPhase_sub_one_le ((n : ℝ) * (1 / H))
  rw [abs_of_pos (mul_pos hnR (one_div_pos.mpr hHR))] at hc
  have hprod := mul_le_mul hc hbound (norm_nonneg _)
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ((n : ℝ) * (1 / H)))
  calc
    _ ≤ (2 * Real.pi * ((n : ℝ) * (1 / H))) * (A * Real.sqrt n) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hprod (sq_nonneg _)
    _ = (2 * Real.pi * A / H) * (n : ℝ) * Real.sqrt n / (n : ℝ) ^ 2 := by ring
    _ = (2 * Real.pi * A / H) / Real.sqrt n :=
      low_sqrt_weight hnR.ne' ht.ne' (Real.sq_sqrt hnR.le)
    _ = _ := by ring

private theorem smoothing_term_le_high {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {A : ℝ} {H n : ℕ} (hn : 0 < n)
    (hbound : ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ ≤ A * Real.sqrt n) :
    ‖expPhase ((n : ℝ) * (1 / H)) - 1‖ *
        ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ / (n : ℝ) ^ 2 ≤
      (2 * A) * (1 / ((n : ℝ) * Real.sqrt n)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hprod := mul_le_mul (norm_expPhase_sub_one_le_two ((n : ℝ) * (1 / H)))
    hbound (norm_nonneg _) zero_le_two
  calc
    _ ≤ 2 * (A * Real.sqrt n) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hprod (sq_nonneg _)
    _ = (2 * A) * Real.sqrt n / (n : ℝ) ^ 2 := by ring
    _ = (2 * A) / ((n : ℝ) * Real.sqrt n) :=
      high_sqrt_weight hnR.ne' ht.ne' (Real.sq_sqrt hnR.le)
    _ = _ := by ring

/-- The smoothing Fourier series has size `O(A/√H)` when its finite
exponential sums have a proved `A√n` bound at positive frequencies. -/
theorem tsum_smoothing_majorant_le_of_sqrt_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {A : ℝ} (hA : 0 ≤ A) {H : ℕ} (hH : 0 < H)
    (hbound : ∀ n : ℕ, 0 < n →
      ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ ≤ A * Real.sqrt n) :
    (∑' n : ℕ, ‖expPhase ((n : ℝ) * (1 / H)) - 1‖ *
        ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ / (n : ℝ) ^ 2) ≤
      (4 * Real.pi + 4) * A / Real.sqrt H := by
  let w : ℕ → ℝ := fun n => ‖expPhase ((n : ℝ) * (1 / H)) - 1‖ *
    ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ / (n : ℝ) ^ 2
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  have hs : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr hHR
  have hhead : ∑ n ∈ Finset.range (H + 1), w n ≤ 4 * Real.pi * A / Real.sqrt H := by
    rw [Finset.sum_range_succ']
    have hw0 : w 0 = 0 := by simp only [w, Nat.cast_zero, zero_mul, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_zero]
    rw [hw0, add_zero]
    calc
      _ ≤ ∑ i ∈ Finset.range H, (2 * Real.pi * A / H) * (1 / Real.sqrt (i + 1 : ℕ)) :=
        Finset.sum_le_sum (fun i _ => smoothing_term_le_low s f hH (Nat.zero_lt_succ i)
          (hbound (i + 1) (Nat.zero_lt_succ i)))
      _ = (2 * Real.pi * A / H) * ∑ i ∈ Finset.range H, 1 / Real.sqrt ((i : ℝ) + 1) := by
        rw [Finset.mul_sum]
        simp only [Nat.cast_add, Nat.cast_one]
      _ ≤ (2 * Real.pi * A / H) * (2 * Real.sqrt H) :=
        mul_le_mul_of_nonneg_left (sum_inv_sqrt_range H) (by positivity)
      _ = 4 * Real.pi * A / Real.sqrt H := by
        rw [← Real.sq_sqrt hHR.le]
        rw [Real.sqrt_sq hs.le]
        field_simp
        ring
  have htail : (∑' i : ℕ, w (i + (H + 1))) ≤ 4 * A / Real.sqrt H := by
    have hsumm : Summable (fun i : ℕ => 1 /
        (((H : ℝ) + i + 1) * Real.sqrt ((H : ℝ) + i + 1))) :=
      summable_of_sum_range_le (fun i => by positivity) (sum_inv_mul_sqrt_tail_le hH)
    have htailbound : ∀ i : ℕ, w (i + (H + 1)) ≤ (2 * A) *
        (1 / (((H : ℝ) + i + 1) * Real.sqrt ((H : ℝ) + i + 1))) := by
      intro i
      have hn : 0 < i + (H + 1) := by omega
      have h := smoothing_term_le_high s f (H := H) hn (hbound _ hn)
      convert h using 1
      push_cast
      ring_nf
    calc
      _ ≤ ∑' i : ℕ, (2 * A) *
          (1 / (((H : ℝ) + i + 1) * Real.sqrt ((H : ℝ) + i + 1))) := by
        apply Summable.tsum_le_tsum htailbound
        · exact (summable_smoothing_majorant s f (1 / H)).comp_injective
            (fun i j hij => Nat.add_right_cancel hij)
        · exact hsumm.mul_left _
      _ = (2 * A) * ∑' i : ℕ, 1 /
          (((H : ℝ) + i + 1) * Real.sqrt ((H : ℝ) + i + 1)) := tsum_mul_left
      _ ≤ (2 * A) * (2 / Real.sqrt H) :=
        mul_le_mul_of_nonneg_left (tsum_inv_mul_sqrt_tail_le hH) (by positivity)
      _ = _ := by ring
  have hsplit := (summable_smoothing_majorant s f (1 / H)).sum_add_tsum_nat_add (H + 1)
  change (∑ n ∈ Finset.range (H + 1), w n) + (∑' i : ℕ, w (i + (H + 1))) = _ at hsplit
  rw [← hsplit]
  calc
    _ ≤ 4 * Real.pi * A / Real.sqrt H + 4 * A / Real.sqrt H := add_le_add hhead htail
    _ = _ := by ring

private theorem smoothing_scale_algebra {n t p C A : ℝ} (ht : t ≠ 0) (hp : p ≠ 0)
    (heq : t ^ 2 = n) :
    (C * A / t) / (2 * (1 / n) * p ^ 2) = (C / (2 * p ^ 2)) * A * t := by
  rw [← heq]
  field_simp

/-- Explicit summed sawtooth bound from an `A√n` frequency bound.
This is a conditional Fourier inequality, not the circle problem. -/
theorem abs_sum_sawtooth_le_of_sqrt_exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {A : ℝ} (hA : 0 ≤ A) {H : ℕ} (hH : 0 < H)
    (hbound : ∀ n : ℕ, 0 < n →
      ‖∑ i ∈ s, expPhase ((n : ℝ) * f i)‖ ≤ A * Real.sqrt n) :
    |∑ i ∈ s, sawtooth (f i)| ≤ (s.card : ℝ) / (2 * H) +
      ((2 * Real.pi + 2) / Real.pi ^ 2) * A * Real.sqrt H := by
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  have hs : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr hHR
  have h := abs_sum_sawtooth_le_smoothing_series s f (one_div_pos.mpr hHR)
  have hD := tsum_smoothing_majorant_le_of_sqrt_bound s f hA hH hbound
  have hden : 0 ≤ 2 * (1 / (H : ℝ)) * Real.pi ^ 2 := by positivity
  have hDdiv := div_le_div_of_nonneg_right hD hden
  have hhead : (s.card : ℝ) * ((1 / H) / 2) = (s.card : ℝ) / (2 * H) := by ring
  rw [hhead] at h
  refine h.trans (add_le_add le_rfl ?_)
  calc
    _ ≤ ((4 * Real.pi + 4) * A / Real.sqrt H) / (2 * (1 / H) * Real.pi ^ 2) := hDdiv
    _ = ((4 * Real.pi + 4) / (2 * Real.pi ^ 2)) * A * Real.sqrt H :=
      smoothing_scale_algebra hs.ne' Real.pi_ne_zero (Real.sq_sqrt hHR.le)
    _ = _ := by ring

end WaveTurbulence.NumberTheory
