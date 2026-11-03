/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleBlockIntervals
public import WaveTurbulence.Foundations.Counting.CircleLowHeights
public import WaveTurbulence.Foundations.Counting.DyadicBlocks
import Mathlib.Tactic

/-!
# Uniform sawtooth cancellation on a left semicircle

NT-CIRCLE-v2 goal 2. Disjoint dyadic height blocks, the low-height count,
and the optimized block estimate give the `R^(2/3)` sawtooth bound. The
radius is parameterized as `r³`, so the bound is `326r²` for `r≥1`.
The height-sum comparison with the area of a disc is not asserted here.
-/

public section

namespace WaveTurbulence.Counting

/-- Global sawtooth cancellation on any integer interval in a translated
left semicircle. Constants are independent of both phase translations. -/
theorem circle_left_sawtooth_sum_le {r c t d : ℝ} {a b : ℕ}
    (hr1 : 1 ≤ r) (hleft : c - r ^ 3 ≤ (a : ℝ) + 1 + t)
    (hright : (b : ℝ) + t ≤ c) :
    |∑ k ∈ Finset.Ioc a b,
      NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)| ≤ 326 * r ^ 2 := by
  classical
  have hr : 0 < r := zero_lt_one.trans_le hr1
  let R := r ^ 3
  have hR : 0 < R := pow_pos hr 3
  let g : ℕ → ℝ := fun k => circleHeight R c ((k : ℝ) + t)
  let F : ℕ → ℝ := fun k => NumberTheory.sawtooth (g k + d)
  obtain ⟨J, hcutlo, hcuthi⟩ := exists_dyadic_circle_cutoff hr1
  have hheight : ∀ k ∈ Finset.Ioc a b, g k ≤ R := by
    intro k _
    apply Real.sqrt_le_iff.mpr
    exact ⟨hR.le, sub_le_self _ (sq_nonneg _)⟩
  have hpartition := sum_eq_low_add_dyadic_blocks (Finset.Ioc a b) g F hR.le hheight J
  have hlow : |∑ k ∈ (Finset.Ioc a b).filter (fun k => g k ≤ R / (2 : ℝ) ^ J), F k| ≤
      3 * r ^ 2 :=
    circle_left_low_sawtooth_sum_le (d := d) hr1 (by positivity) hcuthi.le hleft hright
  have hblocks : ∀ j ∈ Finset.range J,
      |∑ k ∈ (Finset.Ioc a b).filter (fun k => R / (2 : ℝ) ^ (j + 1) < g k ∧
        g k ≤ R / (2 : ℝ) ^ j), F k| ≤ 323 * (R / (2 : ℝ) ^ (j + 1)) / r := by
    intro j hj
    have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hj)
    have hdiv := div_le_div_of_nonneg_left hR.le (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
    have hHlo : r ^ 2 ≤ R / (2 : ℝ) ^ (j + 1) := hcutlo.trans hdiv
    have hHhi : R / (2 : ℝ) ^ (j + 1) ≤ R := by
      apply div_le_self hR.le
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have heq : R / (2 : ℝ) ^ j = 2 * (R / (2 : ℝ) ^ (j + 1)) := by
      rw [pow_succ]
      ring
    have h := circle_left_filtered_block_sum_le (d := d) hr1 hHlo hHhi hleft hright
    simpa only [heq] using h
  have hlarge : (∑ j ∈ Finset.range J,
      |∑ k ∈ (Finset.Ioc a b).filter (fun k => R / (2 : ℝ) ^ (j + 1) < g k ∧
        g k ≤ R / (2 : ℝ) ^ j), F k|) ≤ 323 * r ^ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, 323 * (R / (2 : ℝ) ^ (j + 1)) / r :=
        Finset.sum_le_sum hblocks
      _ = (323 / r) * ∑ j ∈ Finset.range J, R / (2 : ℝ) ^ (j + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (323 / r) * R := mul_le_mul_of_nonneg_left (sum_dyadic_heights_le hR.le J) (by positivity)
      _ = 323 * r ^ 2 := by
        dsimp only [R]
        field_simp
  change |∑ k ∈ Finset.Ioc a b, F k| ≤ _
  rw [hpartition]
  calc
    _ ≤ |∑ k ∈ (Finset.Ioc a b).filter (fun k => g k ≤ R / (2 : ℝ) ^ J), F k| +
        ∑ j ∈ Finset.range J,
          |∑ k ∈ (Finset.Ioc a b).filter (fun k => R / (2 : ℝ) ^ (j + 1) < g k ∧
            g k ≤ R / (2 : ℝ) ^ j), F k| :=
      (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ 3 * r ^ 2 + 323 * r ^ 2 := add_le_add hlow hlarge
    _ = _ := by ring

/-- The corresponding right-semicircle estimate, obtained by an exact
reflection of the integer interval and of the real center. -/
theorem circle_right_sawtooth_sum_le {r c t d : ℝ} {a b : ℕ}
    (hr1 : 1 ≤ r) (hleft : c ≤ (a : ℝ) + 1 + t)
    (hright : (b : ℝ) + t ≤ c + r ^ 3) :
    |∑ k ∈ Finset.Ioc a b,
      NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)| ≤ 326 * r ^ 2 := by
  let t' := -t - (a : ℝ) - (b : ℝ) - 1
  have hl : -c - r ^ 3 ≤ (a : ℝ) + 1 + t' := by
    dsimp only [t']
    linarith only [hright]
  have hu : (b : ℝ) + t' ≤ -c := by
    dsimp only [t']
    linarith only [hleft]
  have h := circle_left_sawtooth_sum_le (c := -c) (t := t') (d := d) hr1 hl hu
  have heq : (∑ k ∈ Finset.Ioc a b,
      NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)) =
      ∑ k ∈ Finset.Ioc a b,
        NumberTheory.sawtooth (circleHeight (r ^ 3) (-c) ((k : ℝ) + t') + d) := by
    refine Finset.sum_bij (fun k _ => a + b + 1 - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Ioc] at hk ⊢
      omega
    · intro k hk l hl hkl
      simp only [Finset.mem_Ioc] at hk hl
      omega
    · intro k hk
      refine ⟨a + b + 1 - k, ?_, ?_⟩
      · simp only [Finset.mem_Ioc] at hk ⊢
        omega
      · simp only [Finset.mem_Ioc] at hk
        omega
    · intro k hk
      have hsub : k ≤ a + b + 1 := by
        obtain ⟨_, hkb⟩ := Finset.mem_Ioc.mp hk
        omega
      have hcast : ((a + b + 1 - k : ℕ) : ℝ) = (a : ℝ) + b + 1 - k := by
        rw [Nat.cast_sub hsub]
        push_cast
        ring
      have hh : circleHeight (r ^ 3) (-c) (((a + b + 1 - k : ℕ) : ℝ) + t') =
          circleHeight (r ^ 3) c ((k : ℝ) + t) := by
        dsimp only [circleHeight, t']
        rw [hcast]
        congr 1
        ring
      exact congrArg (fun z => NumberTheory.sawtooth (z + d)) hh.symm
  rw [heq]
  exact h

/-- Uniform cancellation on any integer interval inside the horizontal
projection of a translated circle. This controls both sawtooth sums in the
exact lattice-disc formula, but does not estimate its height sum. -/
theorem circle_sawtooth_sum_le {r c t d : ℝ} {a b : ℕ}
    (hr1 : 1 ≤ r) (hleft : c - r ^ 3 ≤ (a : ℝ) + 1 + t)
    (hright : (b : ℝ) + t ≤ c + r ^ 3) :
    |∑ k ∈ Finset.Ioc a b,
      NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)| ≤ 652 * r ^ 2 := by
  by_cases hL : (b : ℝ) + t ≤ c
  · have h := circle_left_sawtooth_sum_le (d := d) hr1 hleft hL
    nlinarith only [h, sq_nonneg r]
  by_cases hR : c ≤ (a : ℝ) + 1 + t
  · have h := circle_right_sawtooth_sum_le (d := d) hr1 hR hright
    nlinarith only [h, sq_nonneg r]
  have hxa : (a : ℝ) + 1 + t < c := lt_of_not_ge hR
  have hxb : c < (b : ℝ) + t := lt_of_not_ge hL
  have hx0 : 0 ≤ c - t := by
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith only [hxa, ha]
  let m := ⌊c - t⌋₊
  have ham : a ≤ m := (Nat.le_floor_iff hx0).mpr (by linarith only [hxa])
  have hfloor : (m : ℝ) ≤ c - t := Nat.floor_le hx0
  have hmbR : (m : ℝ) < b := by linarith only [hfloor, hxb]
  have hmb : m ≤ b := (show m < b by exact_mod_cast hmbR).le
  have hml : (m : ℝ) + t ≤ c := by linarith only [hfloor]
  have hmr : c ≤ (m : ℝ) + 1 + t := by
    have h := Nat.lt_floor_add_one (c - t)
    change c - t < (m : ℝ) + 1 at h
    linarith only [h]
  have hlow := circle_left_sawtooth_sum_le (d := d) hr1 hleft hml
  have hhigh := circle_right_sawtooth_sum_le (d := d) hr1 hmr hright
  rw [← Finset.sum_Ioc_consecutive
    (fun k : ℕ => NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)) ham hmb]
  calc
    _ ≤ |∑ k ∈ Finset.Ioc a m,
          NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)| +
        |∑ k ∈ Finset.Ioc m b,
          NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)| := abs_add_le _ _
    _ ≤ 326 * r ^ 2 + 326 * r ^ 2 := add_le_add hlow hhigh
    _ = _ := by ring

end WaveTurbulence.Counting
