/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.RationalCounting

/-!
# Quantitative major-arc counting

The coarse and error-sensitive residue estimates are normalized here to the
scale used by the quadratic interval sum. We use `1 + log K`, which is
positive at `K = 1` and equivalent to `log(2K)` up to absolute constants.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- Harmonic sums at a bounded multiple of `K` have logarithmic size. -/
theorem harmonic_le_eight_log {K m : ℕ} (hK : 1 ≤ K) (hm : m ≤ 8 * K) :
    (harmonic m : ℝ) ≤ 8 * (1 + Real.log K) := by
  have hK' : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK'
  by_cases hm0 : m = 0
  · subst m
    simp only [harmonic_zero, Rat.cast_zero]
    positivity
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK'
  have hm8 : (m : ℝ) ≤ 8 * K := by exact_mod_cast hm
  have hlog8 : Real.log 8 ≤ (7 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    norm_num at h ⊢
    exact h
  calc
    _ ≤ 1 + Real.log m := harmonic_le_one_add_log m
    _ ≤ 1 + Real.log (8 * K) := add_le_add_right (Real.log_le_log hm' hm8) 1
    _ = 1 + (Real.log 8 + Real.log K) := by rw [Real.log_mul (by norm_num) hKpos.ne']
    _ ≤ 8 * (1 + Real.log K) := by linarith only [hlog8, hlogK]

/-- Total capped reciprocal mass of linear frequencies. The cap at zero is
part of the definition, so exact rational resonances contribute `N`. -/
@[expose] noncomputable def frequencyMass (s : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ range N, cappedInv N ‖(s * (m : ℝ) : AddCircle (1 : ℝ))‖

theorem frequencyMass_nonneg (s : ℝ) (N : ℕ) : 0 ≤ frequencyMass s N :=
  sum_nonneg (fun _ _ => cappedInv_nonneg (Nat.cast_nonneg _) _)

/-- Both counting estimates needed for the sharp Gauss bound. Constants are
absolute. No near-resonance estimate is a hypothesis. -/
theorem frequencyMass_bounds (s : ℝ) (a : ℤ) {q K : ℕ}
    (hK : 1 ≤ K) (hq : 1 ≤ q) (hqK : q ≤ K) (ha : a.natAbs.Coprime q)
    (happrox : |s - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * K)) :
    frequencyMass s (2 * K + 2) * q ≤ 1000 * (K : ℝ) ^ 2 * (1 + Real.log K) ∧
      frequencyMass s (2 * K + 2) * q * |s - (a : ℝ) / q| ≤
        1000 * (1 + Real.log K) := by
  let N : ℕ := 2 * K + 2
  let M : ℝ := ((N / q + 1 : ℕ) : ℝ)
  let β : ℝ := |s - (a : ℝ) / q|
  let H : ℝ := 1 + Real.log K
  have hK' : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK'
  have hqK' : (q : ℝ) ≤ K := Nat.cast_le.mpr hqK
  have hH : 1 ≤ H := by dsimp [H]; exact le_add_of_nonneg_right (Real.log_nonneg hK')
  have hβ : 0 ≤ β := abs_nonneg _
  have hβK : β * q * K ≤ 1 := by
    have h := (le_div_iff₀ (mul_pos hq' hKpos)).mp happrox
    simpa only [mul_assoc] using h
  have hN : (N : ℝ) ≤ 4 * K := by dsimp [N]; push_cast; linarith only [hK']
  have hMq : M * q ≤ 5 * K := by
    have h : (N / q + 1) * q ≤ N + q := by
      rw [add_mul, one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self N q) q
    have h' : M * q ≤ (N : ℝ) + q := by dsimp [M]; exact_mod_cast h
    linarith only [h', hN, hqK']
  have hMq0 : 0 ≤ M * q := by dsimp [M]; positivity
  have hbig : (harmonic (N + 4) : ℝ) ≤ 8 * H :=
    harmonic_le_eight_log hK (by dsimp [N]; omega)
  have hsmall : (harmonic (N / q + 1) : ℝ) ≤ 8 * H := by
    apply harmonic_le_eight_log hK
    have hd := Nat.div_le_self N q
    dsimp [N] at hd ⊢
    omega
  have hbig0 : 0 ≤ (harmonic (N + 4) : ℝ) := by
    rw [← sum_inv_range_succ]
    exact sum_nonneg (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j))
  have happN : β * N ≤ 4 / q := by
    apply (le_div_iff₀ hq').mpr
    have h := mul_le_mul_of_nonneg_right hN (mul_nonneg hβ hq'.le)
    nlinarith only [h, hβK]
  have hqN : q ≤ N := by dsimp [N]; omega
  constructor
  · have hc := sum_cappedInv_frequency_le_coarse s (N : ℝ) a
      (Nat.zero_lt_of_lt hq) hqN ha (Nat.cast_nonneg N) happN
    have hc' := mul_le_mul_of_nonneg_right hc hq'.le
    change frequencyMass s N * q ≤ 1000 * (K : ℝ) ^ 2 * H
    calc
      _ ≤ (17 * M * N + 4 * M * q * (harmonic (N + 4) : ℝ)) * q := hc'
      _ = 17 * (M * q) * N + 4 * (M * q) * q * (harmonic (N + 4) : ℝ) := by ring
      _ ≤ 17 * (5 * K) * (4 * K) + 4 * (5 * K) * K * (8 * H) := by
        gcongr
      _ ≤ 1000 * (K : ℝ) ^ 2 * H := by
        have hKH := mul_le_mul_of_nonneg_left hH (sq_nonneg (K : ℝ))
        nlinarith only [hKH, sq_nonneg (K : ℝ)]
  · change frequencyMass s N * q * β ≤ 1000 * H
    by_cases hβzero : β = 0
    · rw [hβzero, mul_zero]
      linarith only [hH]
    have hdiff : s - (a : ℝ) / q ≠ 0 := fun h => hβzero (by dsimp [β]; rw [h, abs_zero])
    have hbpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβzero)
    have hNβ : (N : ℝ) * q * β ≤ 4 := by
      have h := mul_le_mul_of_nonneg_right hN (mul_nonneg hq'.le hβ)
      nlinarith only [h, hβK]
    have hMβ : M * q * q * β ≤ 5 := by
      have h := mul_le_mul_of_nonneg_right hMq (mul_nonneg hq'.le hβ)
      nlinarith only [h, hβK]
    have hr := sum_cappedInv_frequency_le_refined s (N : ℝ) a
      (Nat.zero_lt_of_lt hq) hqN ha (Nat.cast_nonneg N) happN hdiff
    have hr' := mul_le_mul_of_nonneg_right hr (mul_nonneg hq'.le hβ)
    calc
      _ ≤ (17 * ((N : ℝ) + 4 / (β * q) * (harmonic (N / q + 1) : ℝ)) +
          4 * M * q * (harmonic (N + 4) : ℝ)) * (q * β) := by
        simpa only [frequencyMass, β, M, mul_assoc] using hr'
      _ = 17 * ((N : ℝ) * q * β) + 68 * (harmonic (N / q + 1) : ℝ) +
          4 * (M * q * q * β) * (harmonic (N + 4) : ℝ) := by
        field_simp [hbpos.ne', hq'.ne']
        ring
      _ ≤ 17 * 4 + 68 * (8 * H) + 4 * 5 * (8 * H) := by
        gcongr
      _ ≤ 1000 * H := by linarith only [hH]

end WaveTurbulence.WeylSums
