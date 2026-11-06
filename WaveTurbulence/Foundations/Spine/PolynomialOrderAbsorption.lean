/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! Fixed polynomial costs in order are bounded by one geometric factor, uniformly in the order. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Filter Finset
open scoped Topology

theorem exists_pow_le_geometric (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ k ≤ C * 2 ^ n := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
  have he : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ k / 2 ^ n ≤ 1 :=
    (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let C : ℝ := 1 + ∑ n ∈ range N, (n : ℝ) ^ k
  have hC : 1 ≤ C := by
    have hs : 0 ≤ ∑ n ∈ range N, (n : ℝ) ^ k := sum_nonneg fun n _ => pow_nonneg (Nat.cast_nonneg _) _
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp (hN n hn)
    have hh' : (n : ℝ) ^ k ≤ 2 ^ n := by simpa only [one_mul] using hh
    exact hh'.trans (le_mul_of_one_le_left (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) hC)
  · have hh : (n : ℝ) ^ k ≤ ∑ a ∈ range N, (a : ℝ) ^ k :=
      single_le_sum (s := range N) (f := fun a : ℕ => (a : ℝ) ^ k)
        (fun a _ => pow_nonneg (Nat.cast_nonneg _) _) (mem_range.mpr (Nat.lt_of_not_ge hn))
    have hh' : (n : ℝ) ^ k ≤ C := by dsimp only [C]; linarith
    exact hh'.trans (le_mul_of_one_le_right (zero_le_one.trans hC) (one_le_pow₀ (by norm_num)))

theorem exists_succ_pow_le_geometric (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ((n : ℝ) + 1) ^ k ≤ C * 2 ^ n := by
  obtain ⟨C, hC, hb⟩ := exists_pow_le_geometric k
  refine ⟨2 * C, by linarith, ?_⟩
  intro n
  have hh := hb (n + 1)
  simpa only [Nat.cast_add, Nat.cast_one, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hh

end WaveTurbulence.LGSpine
