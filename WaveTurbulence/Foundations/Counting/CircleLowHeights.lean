/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleBlockGeometry
public import WaveTurbulence.Foundations.NumberTheory.Sawtooth
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Counting the low-height part of a circular arc

NT-CIRCLE-v2 goal 2. The columns on a left semicircle with height at most
`L` have cardinality at most `L²/R+1`. For radius `r³` and cutoff `L≤2r²`,
their sawtooth contribution is at most `3r²` when `r≥1`.
-/

public section

namespace WaveTurbulence.Counting

/-- A low-height portion has small horizontal width and hence few columns. -/
theorem card_circle_left_low_heights_le {R c t L : ℝ} {a b : ℕ}
    (hR : 0 < R) (hleft : c - R ≤ (a : ℝ) + 1 + t) (hright : (b : ℝ) + t ≤ c) :
    (((Finset.Ioc a b).filter (fun k : ℕ => circleHeight R c ((k : ℝ) + t) ≤ L)).card : ℝ) ≤
      L ^ 2 / R + 1 := by
  classical
  let T := (Finset.Ioc a b).filter (fun k : ℕ => circleHeight R c ((k : ℝ) + t) ≤ L)
  change (T.card : ℝ) ≤ _
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty, Nat.cast_zero]
    positivity
  · let n0 := T.min' hne
    let n1 := T.max' hne
    have hn0 := Finset.mem_filter.mp (T.min'_mem hne)
    have hn1 := Finset.mem_filter.mp (T.max'_mem hne)
    have hn01 : n0 ≤ n1 := T.min'_le_max' hne
    have hsub : T ⊆ Finset.Icc n0 n1 := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨T.min'_le k hk, T.le_max' k hk⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hcR : (T.card : ℝ) ≤ (n1 : ℝ) - n0 + 1 := by
      have h := (Nat.cast_le (α := ℝ)).mpr hc
      rw [Nat.cast_sub (by omega : n0 ≤ n1 + 1)] at h
      push_cast at h
      linarith only [h]
    have hstart : c - R ≤ (n0 : ℝ) + t := by
      have hna : (a : ℝ) + 1 ≤ n0 := by exact_mod_cast (Finset.mem_Ioc.mp hn0.1).1
      linarith only [hna, hleft]
    have hend : (n1 : ℝ) + t ≤ c := by
      have hnb : (n1 : ℝ) ≤ b := by exact_mod_cast (Finset.mem_Ioc.mp hn1.1).2
      linarith only [hnb, hright]
    have hxy : (n0 : ℝ) + t ≤ (n1 : ℝ) + t := by
      have h : (n0 : ℝ) ≤ n1 := by exact_mod_cast hn01
      linarith only [h]
    have hh : circleHeight R c ((n1 : ℝ) + t) ≤ 2 * (L / 2) := by
      linarith only [hn1.2]
    have hw := circle_left_width_le hR hstart hxy hend hh
    rw [show 4 * (L / 2) ^ 2 / R = L ^ 2 / R by ring] at hw
    linarith only [hcR, hw]

/-- The low part contributes at most `3r²` at the natural circle cutoff. -/
theorem circle_left_low_sawtooth_sum_le {r c t d L : ℝ} {a b : ℕ}
    (hr1 : 1 ≤ r) (hL : 0 ≤ L) (hLhi : L ≤ 2 * r ^ 2)
    (hleft : c - r ^ 3 ≤ (a : ℝ) + 1 + t) (hright : (b : ℝ) + t ≤ c) :
    |∑ k ∈ (Finset.Ioc a b).filter (fun k : ℕ => circleHeight (r ^ 3) c ((k : ℝ) + t) ≤ L),
      NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)| ≤ 3 * r ^ 2 := by
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hR : 0 < r ^ 3 := pow_pos hr 3
  let T := (Finset.Ioc a b).filter (fun k : ℕ => circleHeight (r ^ 3) c ((k : ℝ) + t) ≤ L)
  have hc := card_circle_left_low_heights_le (L := L) hR hleft hright
  have hLsquared := pow_le_pow_left₀ hL hLhi 2
  have hnum : L ^ 2 / r ^ 3 ≤ 4 * r := by
    rw [div_le_iff₀ hR]
    nlinarith only [hLsquared]
  have hr2 : r ≤ r ^ 2 := by
    have hp := mul_nonneg hr.le (sub_nonneg.mpr hr1)
    nlinarith only [hp]
  have hc' : (T.card : ℝ) ≤ 6 * r ^ 2 := by
    change (((Finset.Ioc a b).filter _).card : ℝ) ≤ _
    nlinarith only [hc, hnum, hr1, hr2]
  calc
    _ ≤ ∑ k ∈ T, |NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ T, (1 / 2 : ℝ) :=
      Finset.sum_le_sum (fun k _ => NumberTheory.abs_sawtooth_le_half _)
    _ = (T.card : ℝ) * (1 / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * r ^ 2 := by linarith only [hc']

end WaveTurbulence.Counting
