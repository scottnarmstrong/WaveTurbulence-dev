/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.RealArcCover

/-! # Numerator counting away from the zero rational arc -/

public section
open Finset
namespace WaveTurbulence.WeylSums

/-- Nonzero numerators in a short window; both signs are retained. -/
@[expose] noncomputable def localNumerators (T : ℝ) (q : ℕ) : Finset ℤ :=
  (Icc (-(⌊2 * (q : ℝ) * T⌋₊ : ℤ)) (⌊2 * (q : ℝ) * T⌋₊ : ℤ)).erase 0

theorem localNumerators_card_le {T : ℝ} (hT : 0 ≤ T) (q : ℕ) :
    ((localNumerators T q).card : ℝ) ≤ 4 * q * T := by
  have hc : (localNumerators T q).card = 2 * ⌊2 * (q : ℝ) * T⌋₊ := by
    unfold localNumerators
    rw [card_erase_of_mem (mem_Icc.mpr ⟨by omega, by omega⟩), Int.card_Icc]
    omega
  rw [hc]
  push_cast
  have hf := Nat.floor_le (by positivity : 0 ≤ 2 * (q : ℝ) * T)
  linarith

/-- Away from `|t|≤1/L`, every selected numerator is nonzero, and only
`O(qT)` numerators are possible when `|t|≤T`. -/
theorem exists_approx_local {L T t : ℝ} (hL : 2 ≤ L)
    (ht : 1 / L < |t|) (htT : |t| ≤ T) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ ⌊L⌋₊ ∧ a.natAbs.Coprime q ∧
      a ∈ localNumerators T q ∧ |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * L) := by
  obtain ⟨a, q, hq, hqN, ha, herr⟩ := exists_coprime_approx_real t (by linarith : 1 ≤ L)
  have hLpos : 0 < L := by linarith
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsmall : 1 / ((q : ℝ) * L) ≤ 1 / L := by
    apply one_div_le_one_div_of_le hLpos
    nlinarith
  have ha0 : a ≠ 0 := by
    intro hz
    subst a
    simp only [Int.cast_zero, zero_div, sub_zero] at herr
    exact (not_le_of_gt ht) (herr.trans hsmall)
  have hdist : |(a : ℝ)| ≤ q * |t| + 1 / L := by
    have hm := mul_le_mul_of_nonneg_left herr hqpos.le
    have heq : (q : ℝ) * |t - (a : ℝ) / q| = |(q : ℝ) * t - a| := by
      rw [← abs_of_pos hqpos, ← abs_mul, abs_of_pos hqpos]
      congr 1
      field_simp
    rw [heq] at hm
    have hr : (q : ℝ) * (1 / ((q : ℝ) * L)) = 1 / L := by field_simp
    rw [hr] at hm
    have hh := abs_add_le ((a : ℝ) - q * t) (q * t)
    rw [sub_add_cancel, abs_sub_comm, abs_mul, abs_of_pos hqpos] at hh
    linarith
  have haone : (1 : ℝ) ≤ |(a : ℝ)| := by
    have hz : (1 : ℤ) ≤ |a| := Int.one_le_abs ha0
    exact_mod_cast hz
  have hhalf : 1 / L ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hL
  have haT : |(a : ℝ)| ≤ 2 * q * T := by
    have hqt := mul_le_mul_of_nonneg_left htT hqpos.le
    linarith
  have habs : a.natAbs ≤ ⌊2 * (q : ℝ) * T⌋₊ := by
    apply Nat.le_floor
    simpa only [Nat.cast_natAbs, Int.cast_abs] using haT
  refine ⟨a, q, hq, hqN, ha, ?_, herr⟩
  apply mem_erase.mpr
  refine ⟨ha0, mem_Icc.mpr ?_⟩
  have hz : |a| ≤ (⌊2 * (q : ℝ) * T⌋₊ : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr habs)
  exact abs_le.mp hz

end WaveTurbulence.WeylSums
