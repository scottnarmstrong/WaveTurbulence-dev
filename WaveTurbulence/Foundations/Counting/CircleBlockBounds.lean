/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleSawtooth
public import WaveTurbulence.Foundations.Counting.CircleBlockGeometry
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Simplified local circular sawtooth bounds

NT-CIRCLE-v2 goal 2. On one semicircle the geometric width bound gives a
square-root frequency constant at most `160√H` for a height block `[H,2H]`.
This is still a local block estimate; the global block decomposition and
area comparison are separate obligations.
-/

public section

namespace WaveTurbulence.Counting

private theorem sqrt_circle_curvature {R H : ℝ} (hR : 0 < R) (hH : 0 < H) :
    Real.sqrt (R ^ 2 / (8 * H ^ 3)) = R / (Real.sqrt 8 * H * Real.sqrt H) := by
  rw [Real.sqrt_div (sq_nonneg R), Real.sqrt_sq hR.le,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
  rw [show H ^ 3 = H ^ 2 * H by ring, Real.sqrt_mul (sq_nonneg H), Real.sqrt_sq hH.le]
  congr 1
  ring

private theorem block_amplitude_le {R H N : ℝ} (hR : 0 < R) (hH : 0 < H)
    (hHR : H ≤ R) (hN : N ≤ 4 * H ^ 2 / R) :
    8 * (8 * N * Real.sqrt (R ^ 2 / (8 * H ^ 3)) +
      1 / Real.sqrt (R ^ 2 / (8 * H ^ 3))) ≤ 160 * Real.sqrt H := by
  have hs : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have h8pos : 0 < Real.sqrt (8 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h8lo : (2 : ℝ) ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
  have h8hi : Real.sqrt (8 : ℝ) ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [sqrt_circle_curvature hR hH]
  have hfirst : N * (R / (Real.sqrt 8 * H * Real.sqrt H)) ≤ 2 * Real.sqrt H := by
    calc
      _ ≤ (4 * H ^ 2 / R) * (R / (Real.sqrt 8 * H * Real.sqrt H)) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
      _ = 4 * Real.sqrt H / Real.sqrt 8 := by
        field_simp
        rw [Real.sq_sqrt hH.le]
      _ ≤ 2 * Real.sqrt H := by
        rw [div_le_iff₀ h8pos]
        nlinarith only [mul_le_mul_of_nonneg_right h8lo hs.le]
  have hsecond : 1 / (R / (Real.sqrt 8 * H * Real.sqrt H)) ≤ 3 * Real.sqrt H := by
    rw [one_div_div, div_le_iff₀ hR]
    have hmul := mul_le_mul h8hi hHR hH.le (by norm_num : (0 : ℝ) ≤ 3)
    have h := mul_le_mul_of_nonneg_right hmul hs.le
    nlinarith only [h]
  nlinarith only [hfirst, hsecond, hs.le]

/-- Local sawtooth estimate when an interval on the left semicircle stays
in a height block `[H,2H]`. All hypotheses are geometric or typing data. -/
theorem circle_left_block_sawtooth_sum_le {R c t d H : ℝ} {a b K : ℕ}
    (hab : a ≤ b) (hR : 0 < R) (hH : 0 < H) (hHR : H ≤ R) (hK : 0 < K)
    (hleft : c - R ≤ (a : ℝ) + 1 + t) (hright : (b : ℝ) + 1 + t ≤ c)
    (hblock : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1),
      circleHeight R c (x + t) ∈ Set.Icc H (2 * H)) :
    |∑ k ∈ Finset.Ioc a b, NumberTheory.sawtooth (circleHeight R c ((k : ℝ) + t) + d)| ≤
      ((b : ℝ) - a) / (2 * K) +
        ((2 * Real.pi + 2) / Real.pi ^ 2) * (160 * Real.sqrt H) * Real.sqrt K := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hend : (b : ℝ) + 1 ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1) :=
    ⟨by linarith only [habR], le_rfl⟩
  have hwidth := circle_left_width_le hR hleft
    (show (a : ℝ) + 1 + t ≤ (b : ℝ) + 1 + t by linarith only [habR]) hright
    (hblock _ hend).2
  have hN : (b : ℝ) - a ≤ 4 * H ^ 2 / R := by linarith only [hwidth]
  have hA := block_amplitude_le hR hH hHR hN
  have h := circle_arc_sawtooth_sum_le (d := d) hab hR hH hK hblock
  refine h.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA (by positivity)) (Real.sqrt_nonneg _)

private theorem choose_smoothing_cutoff {r H : ℝ} (hr : 0 < r) (hH : r ^ 2 ≤ H) :
    ∃ K : ℕ, 0 < K ∧ H / r ^ 2 ≤ K ∧ (K : ℝ) ≤ 2 * H / r ^ 2 ∧
      Real.sqrt H * Real.sqrt K ≤ 2 * H / r := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hHpos : 0 < H := hr2.trans_le hH
  have hratio : 1 ≤ H / r ^ 2 := (le_div_iff₀ hr2).mpr (by simpa only [one_mul] using hH)
  let K := ⌈H / r ^ 2⌉₊
  have hlo : H / r ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKposR : 0 < (K : ℝ) := zero_lt_one.trans_le (hratio.trans hlo)
  have hKpos : 0 < K := by exact_mod_cast hKposR
  have hhi : (K : ℝ) ≤ 2 * H / r ^ 2 := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ H / r ^ 2 from div_nonneg hHpos.le hr2.le)
    change (K : ℝ) < H / r ^ 2 + 1 at hlt
    rw [show 2 * H / r ^ 2 = 2 * (H / r ^ 2) by ring]
    linarith only [hlt, hratio]
  refine ⟨K, hKpos, hlo, hhi, ?_⟩
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (div_nonneg (by positivity) hr.le)).mp
  rw [mul_pow, Real.sq_sqrt hHpos.le, Real.sq_sqrt (Nat.cast_nonneg K)]
  have h := mul_le_mul_of_nonneg_left hhi hHpos.le
  have hp : 0 ≤ H ^ 2 / r ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [show H * (2 * H / r ^ 2) = 2 * (H ^ 2 / r ^ 2) by ring] at h
  rw [show (2 * H / r) ^ 2 = 4 * (H ^ 2 / r ^ 2) by ring]
  linarith only [h, hp]

private theorem smoothing_pi_constant_le_one :
    (2 * Real.pi + 2) / Real.pi ^ 2 ≤ 1 := by
  rw [div_le_one (sq_pos_of_pos Real.pi_pos)]
  nlinarith only [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]

/-- Optimizing the cutoff on one left height block. The radius is written
`r³`, so blocks above height `r²` have error at most `322 H/r`. The eventual
global circle estimate must still sum a disjoint covering by such blocks. -/
theorem circle_left_block_sawtooth_sum_le_optimized {r c t d H : ℝ} {a b : ℕ}
    (hab : a ≤ b) (hr : 0 < r) (hHlo : r ^ 2 ≤ H) (hHhi : H ≤ r ^ 3)
    (hleft : c - r ^ 3 ≤ (a : ℝ) + 1 + t) (hright : (b : ℝ) + 1 + t ≤ c)
    (hblock : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1),
      circleHeight (r ^ 3) c (x + t) ∈ Set.Icc H (2 * H)) :
    |∑ k ∈ Finset.Ioc a b, NumberTheory.sawtooth (circleHeight (r ^ 3) c ((k : ℝ) + t) + d)| ≤
      322 * H / r := by
  have hR : 0 < r ^ 3 := pow_pos hr 3
  have hH : 0 < H := (sq_pos_of_pos hr).trans_le hHlo
  obtain ⟨K, hK, hKlo, _, hroot⟩ := choose_smoothing_cutoff hr hHlo
  have h := circle_left_block_sawtooth_sum_le (d := d) hab hR hH hHhi hK hleft hright hblock
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hend : (b : ℝ) + 1 ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1) :=
    ⟨by linarith only [habR], le_rfl⟩
  have hwidth := circle_left_width_le hR hleft
    (show (a : ℝ) + 1 + t ≤ (b : ℝ) + 1 + t by linarith only [habR]) hright
    (hblock _ hend).2
  have hN : (b : ℝ) - a ≤ 4 * H ^ 2 / r ^ 3 := by linarith only [hwidth]
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hhead : ((b : ℝ) - a) / (2 * K) ≤ 2 * H / r := by
    calc
      _ ≤ (4 * H ^ 2 / r ^ 3) / (2 * K) :=
        div_le_div_of_nonneg_right hN (by positivity)
      _ ≤ (4 * H ^ 2 / r ^ 3) / (2 * (H / r ^ 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hKlo zero_le_two)
      _ = _ := by field_simp; ring
  have hcoef : ((2 * Real.pi + 2) / Real.pi ^ 2) *
      (160 * Real.sqrt H) * Real.sqrt K ≤ 320 * H / r := by
    calc
      _ ≤ (160 * Real.sqrt H) * Real.sqrt K := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_left (by positivity) smoothing_pi_constant_le_one) (Real.sqrt_nonneg _)
      _ = 160 * (Real.sqrt H * Real.sqrt K) := by ring
      _ ≤ 160 * (2 * H / r) := mul_le_mul_of_nonneg_left hroot (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ 2 * H / r + 320 * H / r := h.trans (add_le_add hhead hcoef)
    _ = _ := by ring

end WaveTurbulence.Counting
