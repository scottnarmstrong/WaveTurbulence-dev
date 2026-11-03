/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ResidueBlocks
public import WaveTurbulence.Foundations.WeylSums.RationalResidues

/-!
# Counting linear frequencies near a rational

Numerator fibers reduce near-resonant frequencies to affine progressions.
The far fibers contribute a harmonic sum. The logarithm convention for the
resulting interval bound is `log(2K)`, including `K = 1`.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- Every residue-numerator fiber lies in one congruence class. -/
theorem exists_residue_fiber (s : ℝ) (a : ℤ) (q N : ℕ) (n : ℤ)
    (ha : a.natAbs.Coprime q) :
    ∃ r, ∀ j ∈ (range N).filter (fun j => residueNumerator s a q j = n), j % q = r := by
  classical
  let S := (range N).filter (fun j => residueNumerator s a q j = n)
  rcases S.eq_empty_or_nonempty with hempty | hne
  · refine ⟨0, ?_⟩
    intro j hj
    change j ∈ S at hj
    rw [hempty] at hj
    simp at hj
  · obtain ⟨i, hi⟩ := hne
    refine ⟨i % q, ?_⟩
    intro j hj
    exact residueNumerator_mod_eq s a ha ((mem_filter.mp hj).2.trans (mem_filter.mp hi).2.symm)

/-- Uniform trivial bound for a single numerator fiber. -/
theorem sum_cappedInv_fiber_le_trivial (s T : ℝ) (a n : ℤ) (q N : ℕ)
    (hq : 0 < q) (ha : a.natAbs.Coprime q) (hT : 0 ≤ T) :
    (∑ j ∈ (range N).filter (fun j => residueNumerator s a q j = n),
      cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖) ≤
      ((N / q + 1 : ℕ) : ℝ) * T := by
  obtain ⟨r, hr⟩ := exists_residue_fiber s a q N n ha
  have heq : ∀ j ∈ (range N).filter (fun j => residueNumerator s a q j = n),
      cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ =
        cappedInv T ((n : ℝ) / q + (s - (a : ℝ) / q) * j) := by
    intro j hj
    rw [norm_frequency_eq_residue s a hq j, (mem_filter.mp hj).2, cappedInv_abs]
  rw [sum_congr rfl heq]
  exact sum_cappedInv_residue_le_trivial _ N q r (fun j hj => mem_range.mp (mem_filter.mp hj).1)
    hr T ((n : ℝ) / q) (s - (a : ℝ) / q) hT

/-- Refined bound for a numerator fiber; its step is `q(s-a/q)`. -/
theorem sum_cappedInv_fiber_le (s T : ℝ) (a n : ℤ) (q N : ℕ)
    (hq : 0 < q) (ha : a.natAbs.Coprime q) (hT : 0 ≤ T)
    (hβ : s - (a : ℝ) / q ≠ 0) :
    (∑ j ∈ (range N).filter (fun j => residueNumerator s a q j = n),
      cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖) ≤
      T + 4 / (|s - (a : ℝ) / q| * q) * (harmonic (N / q + 1) : ℝ) := by
  obtain ⟨r, hr⟩ := exists_residue_fiber s a q N n ha
  have heq : ∀ j ∈ (range N).filter (fun j => residueNumerator s a q j = n),
      cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ =
        cappedInv T ((n : ℝ) / q + (s - (a : ℝ) / q) * j) := by
    intro j hj
    rw [norm_frequency_eq_residue s a hq j, (mem_filter.mp hj).2, cappedInv_abs]
  rw [sum_congr rfl heq]
  exact sum_cappedInv_residue_le _ N q r hq (fun j hj => mem_range.mp (mem_filter.mp hj).1)
    hr T ((n : ℝ) / q) (s - (a : ℝ) / q) hT hβ

/-- Far residue numerators keep their frequencies quantitatively away from integers. -/
theorem cappedInv_frequency_le_of_far_residue (s T : ℝ) (a : ℤ) {q N j : ℕ}
    (hq : 0 < q) (hj : j < N)
    (happrox : |s - (a : ℝ) / q| * N ≤ 4 / q)
    (hfar : 8 < |(residueNumerator s a q j : ℝ)|) :
    cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ ≤
      2 * q / |(residueNumerator s a q j : ℝ)| := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have herr : |(s - (a : ℝ) / q) * j| ≤ 4 / q := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ j from Nat.cast_nonneg j)]
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj.le) (abs_nonneg _)).trans happrox
  have htri : |(residueNumerator s a q j : ℝ)| / q ≤
      ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ + 4 / q := by
    rw [norm_frequency_eq_residue s a hq j]
    calc
      _ = |((residueNumerator s a q j : ℝ) / q + (s - (a : ℝ) / q) * j) -
        (s - (a : ℝ) / q) * j| := by
          rw [add_sub_cancel_right, abs_div, abs_of_pos hq']
      _ ≤ |(residueNumerator s a q j : ℝ) / q + (s - (a : ℝ) / q) * j| +
          |(s - (a : ℝ) / q) * j| := abs_sub _ _
      _ ≤ _ := add_le_add_right herr _
  have hmul : |(residueNumerator s a q j : ℝ)| ≤
      q * ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ + 4 := by
    have h := (div_le_iff₀ hq').mp htri
    rw [add_mul, div_mul_cancel₀ _ hq'.ne'] at h
    simpa only [mul_comm] using h
  have htwice : |(residueNumerator s a q j : ℝ)| ≤
      2 * q * ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ := by
    linarith only [hmul, hfar]
  have hpos : 0 < ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ := by
    by_contra hn
    have hn' := norm_nonneg (s * (j : ℝ) : AddCircle (1 : ℝ))
    have heq : ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ = 0 := le_antisymm (le_of_not_gt hn) hn'
    rw [heq, mul_zero] at htwice
    linarith only [htwice, hfar]
  refine (cappedInv_le_inv T hpos.ne').trans ?_
  rw [abs_of_pos hpos, inv_eq_one_div]
  exact (div_le_div_iff₀ hpos (by linarith only [hfar])).mpr (by simpa using htwice)

/-- The total contribution of a far fiber is its cardinality times its
uniform inverse-distance bound. -/
theorem sum_cappedInv_far_fiber_le (s T : ℝ) (a n : ℤ) (q N : ℕ)
    (hq : 0 < q) (ha : a.natAbs.Coprime q)
    (happrox : |s - (a : ℝ) / q| * N ≤ 4 / q) (hfar : 8 < |(n : ℝ)|) :
    (∑ j ∈ (range N).filter (fun j => residueNumerator s a q j = n),
      cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖) ≤
      ((N / q + 1 : ℕ) : ℝ) * (2 * q / |(n : ℝ)|) := by
  obtain ⟨r, hr⟩ := exists_residue_fiber s a q N n ha
  have hc := card_residue_le ((range N).filter (fun j => residueNumerator s a q j = n)) N q r
    (fun j hj => mem_range.mp (mem_filter.mp hj).1) hr
  calc
    _ ≤ ∑ j ∈ (range N).filter (fun j => residueNumerator s a q j = n),
        2 * q / |(n : ℝ)| := by
      apply sum_le_sum
      intro j hj
      have hj' := (mem_filter.mp hj).2
      have hfar' : 8 < |(residueNumerator s a q j : ℝ)| := by rw [hj']; exact hfar
      simpa only [hj'] using cappedInv_frequency_le_of_far_residue s T a hq
        (mem_range.mp (mem_filter.mp hj).1) happrox hfar'
    _ = (((range N).filter (fun j => residueNumerator s a q j = n)).card : ℝ) *
        (2 * q / |(n : ℝ)|) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)


/-- Exact decomposition into a bounded interval of residue numerators. -/
theorem sum_cappedInv_eq_residue_fibers (s T : ℝ) (a : ℤ) {q N : ℕ}
    (hq : 0 < q) (hqN : q ≤ N)
    (happrox : |s - (a : ℝ) / q| * N ≤ 4 / q) :
    (∑ j ∈ range N, cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖) =
      ∑ n ∈ Icc (-((N + 4 : ℕ) : ℤ)) (N + 4 : ℕ),
        ∑ j ∈ (range N).filter (fun j => residueNumerator s a q j = n),
          cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ := by
  classical
  apply (sum_fiberwise_of_maps_to ?_ _).symm
  intro j hj
  have hb := abs_residueNumerator_le s a hq (mem_range.mp hj) happrox
  have hqN' : (q : ℝ) ≤ N := Nat.cast_le.mpr hqN
  have hb' : |(residueNumerator s a q j : ℝ)| ≤ ((N + 4 : ℕ) : ℝ) := by
    push_cast
    linarith only [hb, hqN', (show (0 : ℝ) ≤ q from Nat.cast_nonneg q)]
  have hbint : |residueNumerator s a q j| ≤ ((N + 4 : ℕ) : ℤ) := by
    exact_mod_cast hb'
  exact mem_Icc.mpr (abs_le.mp hbint)

/-- Coarse rational counting, retaining the `N²/q` major-arc term. -/
theorem sum_cappedInv_frequency_le_coarse (s T : ℝ) (a : ℤ) {q N : ℕ}
    (hq : 0 < q) (hqN : q ≤ N) (ha : a.natAbs.Coprime q) (hT : 0 ≤ T)
    (happrox : |s - (a : ℝ) / q| * N ≤ 4 / q) :
    (∑ j ∈ range N, cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖) ≤
      17 * ((N / q + 1 : ℕ) : ℝ) * T +
        4 * ((N / q + 1 : ℕ) : ℝ) * q * (harmonic (N + 4) : ℝ) := by
  classical
  rw [sum_cappedInv_eq_residue_fibers s T a hq hqN happrox]
  let M : ℝ := ((N / q + 1 : ℕ) : ℝ)
  calc
    _ ≤ ∑ n ∈ Icc (-((N + 4 : ℕ) : ℤ)) (N + 4 : ℕ),
        if |n| ≤ 8 then M * T else (M * 2 * q) / |(n : ℝ)| := by
      apply sum_le_sum
      intro n _
      split_ifs with hn
      · exact sum_cappedInv_fiber_le_trivial s T a n q N hq ha hT
      · have hfar : (8 : ℝ) < |(n : ℝ)| := by exact_mod_cast lt_of_not_ge hn
        calc
          _ ≤ M * (2 * q / |(n : ℝ)|) :=
            sum_cappedInv_far_fiber_le s T a n q N hq ha happrox hfar
          _ = _ := by ring
    _ ≤ 17 * (M * T) + 2 * (M * 2 * q) * (harmonic (N + 4) : ℝ) :=
      sum_int_envelope_le (N + 4) (M * T) (M * 2 * q) (by positivity) (by positivity)
    _ = _ := by dsimp [M]; ring

/-- Refined rational counting, retaining the error-dependent gain `1/(q|β|)`.
Together with the coarse estimate this gives the sharp interval Gauss bound. -/
theorem sum_cappedInv_frequency_le_refined (s T : ℝ) (a : ℤ) {q N : ℕ}
    (hq : 0 < q) (hqN : q ≤ N) (ha : a.natAbs.Coprime q) (hT : 0 ≤ T)
    (happrox : |s - (a : ℝ) / q| * N ≤ 4 / q) (hβ : s - (a : ℝ) / q ≠ 0) :
    (∑ j ∈ range N, cappedInv T ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖) ≤
      17 * (T + 4 / (|s - (a : ℝ) / q| * q) * (harmonic (N / q + 1) : ℝ)) +
        4 * ((N / q + 1 : ℕ) : ℝ) * q * (harmonic (N + 4) : ℝ) := by
  classical
  rw [sum_cappedInv_eq_residue_fibers s T a hq hqN happrox]
  let M : ℝ := ((N / q + 1 : ℕ) : ℝ)
  let A : ℝ := T + 4 / (|s - (a : ℝ) / q| * q) * (harmonic (N / q + 1) : ℝ)
  have hH : 0 ≤ (harmonic (N / q + 1) : ℝ) := by
    rw [← sum_inv_range_succ]
    exact sum_nonneg (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j))
  have hA : 0 ≤ A := add_nonneg hT (mul_nonneg (by positivity) hH)
  calc
    _ ≤ ∑ n ∈ Icc (-((N + 4 : ℕ) : ℤ)) (N + 4 : ℕ),
        if |n| ≤ 8 then A else (M * 2 * q) / |(n : ℝ)| := by
      apply sum_le_sum
      intro n _
      split_ifs with hn
      · exact sum_cappedInv_fiber_le s T a n q N hq ha hT hβ
      · have hfar : (8 : ℝ) < |(n : ℝ)| := by exact_mod_cast lt_of_not_ge hn
        calc
          _ ≤ M * (2 * q / |(n : ℝ)|) :=
            sum_cappedInv_far_fiber_le s T a n q N hq ha happrox hfar
          _ = _ := by ring
    _ ≤ 17 * A + 2 * (M * 2 * q) * (harmonic (N + 4) : ℝ) :=
      sum_int_envelope_le (N + 4) A (M * 2 * q) hA (by positivity)
    _ = _ := by dsimp [A, M]; ring


end WaveTurbulence.WeylSums
