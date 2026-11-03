/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleBlockBounds
public import WaveTurbulence.Foundations.Counting.MonotoneIntervals
import Mathlib.Tactic

/-!
# Exact integer circular height blocks

NT-CIRCLE-v2 goal 2. A half-open height filter of the integer columns of a
left semicircle is an interval. Removing and separately counting its last
point supplies the extra real endpoint required by the derivative test.
The resulting bound includes this endpoint cost explicitly.
-/

public section

namespace WaveTurbulence.Counting

/-- The local optimized bound for the actual filtered integer block.
The last point is retained in the sum and costs at most one half. -/
theorem circle_left_filtered_block_sum_le {r c t d H : ℝ} {a b : ℕ}
    (hr1 : 1 ≤ r) (hHlo : r ^ 2 ≤ H) (hHhi : H ≤ r ^ 3)
    (hleft : c - r ^ 3 ≤ (a : ℝ) + 1 + t) (hright : (b : ℝ) + t ≤ c) :
    |∑ k ∈ (Finset.Ioc a b).filter (fun k : ℕ =>
        H < circleHeight (r ^ 3) c ((k : ℝ) + t) ∧
          circleHeight (r ^ 3) c ((k : ℝ) + t) ≤ 2 * H),
      NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)| ≤
      323 * H / r := by
  classical
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hH : 0 < H := (sq_pos_of_pos hr).trans_le hHlo
  have hpos : 1 ≤ H / r := by
    rw [le_div_iff₀ hr, one_mul]
    have hp := mul_nonneg hr.le (sub_nonneg.mpr hr1)
    nlinarith only [hp, hHlo]
  let g : ℕ → ℝ := fun k => circleHeight (r ^ 3) c ((k : ℝ) + t)
  have hside (k : ℕ) (hk : k ∈ Set.Ioc a b) : (k : ℝ) + t ≤ c := by
    have hkb : (k : ℝ) ≤ b := by exact_mod_cast hk.2
    linarith only [hkb, hright]
  have hmono : MonotoneOn g (Set.Ioc a b) := by
    intro k hk l hl hkl
    apply circleHeight_monotone_left (hside k hk) (hside l hl)
    have hklR : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith only [hklR]
  let T := (Finset.Ioc a b).filter (fun k => H < g k ∧ g k ≤ 2 * H)
  obtain ⟨a', b', ha', hb', hT⟩ := filter_monotone_Ioc_lt_le_eq_Ioc hmono H (2 * H)
  change |∑ k ∈ T, NumberTheory.sawtooth (g k + d)| ≤ 323 * H / r
  change T = Finset.Ioc a' b' at hT
  rw [hT]
  by_cases hab' : a' < b'
  · have hfirst : a' + 1 ∈ T := by
      rw [hT]
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    have hlast : b' ∈ T := by
      rw [hT]
      exact Finset.mem_Ioc.mpr ⟨hab', le_rfl⟩
    have hgfirst : H < g (a' + 1) := (Finset.mem_filter.mp hfirst).2.1
    have hglast : g b' ≤ 2 * H := (Finset.mem_filter.mp hlast).2.2
    have hbpos : 0 < b' := by omega
    have hbcast : ((b' - 1 : ℕ) : ℝ) + 1 = (b' : ℝ) := by
      rw [Nat.cast_sub hbpos, Nat.cast_one]
      ring
    have hfirstside : (a' : ℝ) + 1 + t ≤ c := by
      have ha'le : (a' : ℝ) + 1 ≤ b' := by exact_mod_cast hab'
      have hbR : (b' : ℝ) ≤ b := by exact_mod_cast hb'
      linarith only [ha'le, hbR, hright]
    have hlastside : (b' : ℝ) + t ≤ c := by
      have hbR : (b' : ℝ) ≤ b := by exact_mod_cast hb'
      linarith only [hbR, hright]
    have hblock : ∀ x ∈ Set.Icc ((a' : ℝ) + 1) (((b' - 1 : ℕ) : ℝ) + 1),
        circleHeight (r ^ 3) c (x + t) ∈ Set.Icc H (2 * H) := by
      intro x hx
      rw [hbcast] at hx
      have hxside : x + t ≤ c := by linarith only [hx.2, hlastside]
      have hl := circleHeight_monotone_left (R := r ^ 3) hfirstside hxside
        (show (a' : ℝ) + 1 + t ≤ x + t by linarith only [hx.1])
      have hu := circleHeight_monotone_left (R := r ^ 3) hxside hlastside
        (show x + t ≤ (b' : ℝ) + t by linarith only [hx.2])
      have hgfirst' : H < circleHeight (r ^ 3) c ((a' : ℝ) + 1 + t) := by
        simpa only [g, Nat.cast_add, Nat.cast_one] using hgfirst
      exact ⟨hgfirst'.le.trans hl, hu.trans hglast⟩
    have hleft' : c - r ^ 3 ≤ (a' : ℝ) + 1 + t := by
      have haR : (a : ℝ) ≤ a' := by exact_mod_cast ha'
      linarith only [haR, hleft]
    have hright' : ((b' - 1 : ℕ) : ℝ) + 1 + t ≤ c := by
      rw [hbcast]
      exact hlastside
    have hopt := circle_left_block_sawtooth_sum_le_optimized (d := d)
      (show a' ≤ b' - 1 by omega) hr hHlo hHhi hleft' hright' hblock
    have hsplit : Finset.Ioc a' b' = insert b' (Finset.Ioc a' (b' - 1)) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Ioc]; omega)]
    calc
      _ ≤ |NumberTheory.sawtooth (g b' + d)| +
          |∑ k ∈ Finset.Ioc a' (b' - 1), NumberTheory.sawtooth (g k + d)| := abs_add_le _ _
      _ ≤ (1 / 2 : ℝ) + 322 * H / r :=
        add_le_add (NumberTheory.abs_sawtooth_le_half _) hopt
      _ ≤ 323 * H / r := by
        rw [show 323 * H / r = 322 * H / r + H / r by ring]
        linarith only [hpos]
  · rw [Finset.Ioc_eq_empty hab', Finset.sum_empty, abs_zero]
    positivity

end WaveTurbulence.Counting
