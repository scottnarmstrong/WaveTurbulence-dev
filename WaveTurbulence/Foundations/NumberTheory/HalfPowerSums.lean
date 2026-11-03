/-
Copyright (c) 2026 Jason Hickey, Scott Armstrong. All rights reserved.
Released under Apache 2.0 license; see SALT-LICENSE in this directory.
Authors: Jason Hickey, Claude, Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Half-power sums for Fourier smoothing

Explicit head and tail bounds, proved by telescoping square roots.
The head proof is adapted from Jason Hickey's `Salt/ExpSum/DerivTest.lean`,
commit `3d7274047aabeea823abf1c0bdf675ce165dbca2`, https://github.com/jyh/salt.
The tail estimate is a new proof. These are numerical ingredients for
NT-CIRCLE-v2 goal 2, with no assumed exponential-sum or lattice estimate.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The first `H` reciprocal square roots sum to at most `2√H`. -/
theorem sum_inv_sqrt_range (H : ℕ) :
    ∑ i ∈ Finset.range H, 1 / Real.sqrt ((i : ℝ) + 1) ≤ 2 * Real.sqrt H := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ]
      set s := Real.sqrt (H : ℝ) with hs
      set t := Real.sqrt ((H : ℝ) + 1) with ht
      have hs2 : s ^ 2 = (H : ℝ) := Real.sq_sqrt (Nat.cast_nonneg H)
      have ht2 : t ^ 2 = (H : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have htpos : 0 < t := Real.sqrt_pos.mpr (by positivity)
      have hkey : 1 / t ≤ 2 * (t - s) := by
        rw [div_le_iff₀ htpos]
        linarith only [ht2, hs2, sq_nonneg (t - s)]
      have hcast : Real.sqrt ((H : ℝ) + 1) = Real.sqrt ((H + 1 : ℕ) : ℝ) := by
        push_cast
        ring_nf
      calc
        _ ≤ 2 * s + 1 / t := by linarith only [ih]
        _ ≤ 2 * t := by linarith only [hkey]
        _ = 2 * Real.sqrt ((H + 1 : ℕ) : ℝ) := by rw [ht, hcast]

private theorem inverse_cube_sqrt_step {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (heq : t ^ 2 = s ^ 2 + 1) :
    1 / (t ^ 2 * t) ≤ 2 * (1 / s - 1 / t) := by
  have hp : 0 ≤ (t - s) ^ 2 * (2 * t + s) :=
    mul_nonneg (sq_nonneg _) (by linarith only [hs, ht])
  have heqs := congrArg (fun z : ℝ => s * z) heq
  have hkey : s ≤ 2 * t ^ 2 * (t - s) := by nlinarith only [hp, heqs]
  rw [div_le_iff₀ (mul_pos (pow_pos ht 2) ht)]
  have hid : 2 * (1 / s - 1 / t) * (t ^ 2 * t) = 2 * t ^ 2 * (t - s) / s := by
    field_simp
  rw [hid, le_div_iff₀ hs, one_mul]
  exact hkey

/-- A finite tail of `n^(-3/2)` is at most `2/√H`, uniformly in its length. -/
theorem sum_inv_mul_sqrt_tail_le {H : ℕ} (hH : 0 < H) (N : ℕ) :
    ∑ i ∈ Finset.range N,
      1 / (((H : ℝ) + i + 1) * Real.sqrt ((H : ℝ) + i + 1)) ≤
      2 / Real.sqrt H := by
  have hstep (i : ℕ) :
      1 / (((H : ℝ) + i + 1) * Real.sqrt ((H : ℝ) + i + 1)) ≤
        2 * (1 / Real.sqrt ((H : ℝ) + i) - 1 / Real.sqrt ((H : ℝ) + (i + 1))) := by
    have hbase : 0 < (H : ℝ) + i := by positivity
    have hs : 0 < Real.sqrt ((H : ℝ) + i) := Real.sqrt_pos.mpr hbase
    have ht : 0 < Real.sqrt ((H : ℝ) + i + 1) := Real.sqrt_pos.mpr (by linarith only [hbase])
    have hsq : Real.sqrt ((H : ℝ) + i + 1) ^ 2 =
        Real.sqrt ((H : ℝ) + i) ^ 2 + 1 := by
      rw [Real.sq_sqrt hbase.le, Real.sq_sqrt (by linarith only [hbase])]
    have h := inverse_cube_sqrt_step hs ht hsq
    rw [Real.sq_sqrt (by linarith only [hbase])] at h
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        2 * (1 / Real.sqrt ((H : ℝ) + i) - 1 / Real.sqrt ((H : ℝ) + (i + 1))) :=
      Finset.sum_le_sum (fun i _ => hstep i)
    _ = 2 * (1 / Real.sqrt H - 1 / Real.sqrt ((H : ℝ) + N)) := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] using
        Finset.sum_range_sub' (fun j : ℕ => 1 / Real.sqrt ((H : ℝ) + j)) N
    _ ≤ 2 / Real.sqrt H := by
      have hn : 0 ≤ 1 / Real.sqrt ((H : ℝ) + N) := by positivity
      calc
        _ ≤ 2 * (1 / Real.sqrt H) :=
          mul_le_mul_of_nonneg_left (sub_le_self _ hn) zero_le_two
        _ = _ := by ring

/-- The infinite tail is summable and has the same explicit bound. -/
theorem tsum_inv_mul_sqrt_tail_le {H : ℕ} (hH : 0 < H) :
    (∑' i : ℕ, 1 / (((H : ℝ) + i + 1) * Real.sqrt ((H : ℝ) + i + 1))) ≤
      2 / Real.sqrt H := by
  exact Real.tsum_le_of_sum_range_le (fun i => by positivity) (sum_inv_mul_sqrt_tail_le hH)

end WaveTurbulence.NumberTheory
