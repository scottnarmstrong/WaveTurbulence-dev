/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.RationalArcCover

/-! # Rational approximation at a real lattice scale -/

public section
open Finset
namespace WaveTurbulence.WeylSums

/-- Dirichlet approximation at any real scale at least one. -/
theorem exists_coprime_approx_real (t : ℝ) {L : ℝ} (hL : 1 ≤ L) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ ⌊L⌋₊ ∧ a.natAbs.Coprime q ∧
      |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * L) := by
  have hN : 1 ≤ ⌊L⌋₊ := (Nat.one_le_floor_iff L).mpr hL
  obtain ⟨r, hr, hrN⟩ := Real.exists_rat_abs_sub_le_and_den_le t (Nat.zero_lt_of_lt hN)
  refine ⟨r.num, r.den, r.pos, hrN, r.reduced, ?_⟩
  rw [← Rat.cast_def]
  refine hr.trans ?_
  apply one_div_le_one_div_of_le
  · positivity
  · have hf : L ≤ (⌊L⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one L).le
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg r.den)

/-- Finite numerator range for real-scale Dirichlet approximation. -/
theorem exists_approx_unit_interval_real (t : ℝ) {L : ℝ} (hL : 1 ≤ L)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ ⌊L⌋₊ ∧ a.natAbs.Coprime q ∧
      a ∈ Icc (-1 : ℤ) ((q : ℤ) + 1) ∧ |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * L) := by
  obtain ⟨a, q, hq, hqN, ha, happ⟩ := exists_coprime_approx_real t hL
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  have hden : (q : ℝ) ≤ q * L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hq'.le
  have herr : |t - (a : ℝ) / q| ≤ 1 / (q : ℝ) :=
    happ.trans (one_div_le_one_div_of_le hq' hden)
  obtain ⟨hl, hu⟩ := abs_le.mp herr
  have hl' := mul_le_mul_of_nonneg_right hl hq'.le
  have hu' := mul_le_mul_of_nonneg_right hu hq'.le
  have hmul : (t - (a : ℝ) / q) * q = t * q - a := by field_simp
  rw [hmul, neg_mul, div_mul_cancel₀ _ hq'.ne'] at hl'
  rw [hmul, div_mul_cancel₀ _ hq'.ne'] at hu'
  have htq0 : 0 ≤ t * q := mul_nonneg ht.1 hq'.le
  have htq1 : t * q ≤ q := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hq'.le
  have hal : (-1 : ℝ) ≤ a := by linarith only [hu', htq0]
  have hau : (a : ℝ) ≤ q + 1 := by linarith only [hl', htq1]
  refine ⟨a, q, hq, hqN, ha, mem_Icc.mpr ⟨?_, ?_⟩, happ⟩
  · exact_mod_cast hal
  · exact_mod_cast hau

end WaveTurbulence.WeylSums
