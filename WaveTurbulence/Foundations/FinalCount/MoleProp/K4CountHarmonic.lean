/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.QuadraticStrip
public import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! # Uniform reciprocal-coordinate sums on translated integer intervals

The localized K4 base triple is estimated by fixing a nonzero coefficient
coordinate. Its location is arbitrary; only the interval diameter matters.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

private def signedInitialSegment (N : ℕ) : Finset ℤ :=
  (range N).image (fun j => ((j+1 : ℕ) : ℤ)) ∪
    (range N).image (fun j => -((j+1 : ℕ) : ℤ))

private theorem mem_signedInitialSegment {N : ℕ} {n : ℤ}
    (hn : n ≠ 0) (hbound : |(n : ℝ)| ≤ N) : n ∈ signedInitialSegment N := by
  have hb : -(N : ℤ) ≤ n ∧ n ≤ N := by exact_mod_cast abs_le.mp hbound
  by_cases hp : 0 < n
  · apply mem_union_left
    apply mem_image.mpr
    refine ⟨n.toNat-1,mem_range.mpr (by omega),?_⟩
    omega
  · apply mem_union_right
    apply mem_image.mpr
    refine ⟨(-n).toNat-1,mem_range.mpr (by omega),?_⟩
    omega

private theorem sum_signedInitialSegment (N : ℕ) :
    ∑ n ∈ signedInitialSegment N, |(n : ℝ)|⁻¹ = 2*(harmonic N : ℝ) := by
  have hd : Disjoint ((range N).image (fun j => ((j+1 : ℕ) : ℤ)))
      ((range N).image (fun j => -((j+1 : ℕ) : ℤ))) := by
    apply disjoint_left.mpr
    intro n hn hm
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    obtain ⟨j,hj,he⟩ := mem_image.mp hm
    omega
  rw [signedInitialSegment,sum_union hd,sum_image,sum_image]
  · have ha (n : ℕ) : |((n : ℕ) : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    simp only [Int.cast_neg,Int.cast_natCast,abs_neg,ha,harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    ring
  · intro i _hi j _hj he
    simp only [neg_inj,Int.natCast_inj] at he
    omega
  · intro i _hi j _hj he
    simp only [neg_inj,Int.natCast_inj] at he
    omega

/-- A translated integer interval has a logarithmic reciprocal-coordinate
sum, uniformly in its center. Zero contributes its literal reciprocal 0. -/
theorem k4_sum_inv_abs_le_harmonic (S : Finset ℤ) {N : ℕ} (hN : 0 < N)
    (hcard : (S.card : ℝ) ≤ N) :
    ∑ n ∈ S, |(n : ℝ)|⁻¹ ≤ 2*(harmonic N : ℝ)+1 := by
  classical
  let small := S.filter (fun n : ℤ => |(n : ℝ)| ≤ N)
  let large := S.filter (fun n : ℤ => ¬ |(n : ℝ)| ≤ N)
  have hsmall : ∑ n ∈ small, |(n : ℝ)|⁻¹ ≤ 2*(harmonic N : ℝ) := by
    have hs : small.erase 0 ⊆ signedInitialSegment N := by
      intro n hn
      exact mem_signedInitialSegment (mem_erase.mp hn).1 (mem_filter.mp (mem_erase.mp hn).2).2
    have hh : (∑ n ∈ small.erase 0, |(n : ℝ)|⁻¹) ≤
        ∑ n ∈ signedInitialSegment N, |(n : ℝ)|⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => inv_nonneg.mpr (abs_nonneg _))
    have he : ∑ n ∈ small.erase 0, |(n : ℝ)|⁻¹ = ∑ n ∈ small, |(n : ℝ)|⁻¹ := by
      by_cases hz : (0 : ℤ) ∈ small
      · have he := sum_erase_add small (fun n : ℤ => |(n : ℝ)|⁻¹) hz
        simpa only [Int.cast_zero,abs_zero,inv_zero,add_zero] using he
      · rw [erase_eq_of_notMem hz]
    rw [he,sum_signedInitialSegment] at hh
    exact hh
  have hlarge : ∑ n ∈ large, |(n : ℝ)|⁻¹ ≤ 1 := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have hh : ∑ n ∈ large, |(n : ℝ)|⁻¹ ≤ ∑ _n ∈ large, (N : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      exact (inv_le_inv₀ (hNp.trans (lt_of_not_ge (mem_filter.mp hn).2)) hNp).mpr
        (le_of_not_ge (mem_filter.mp hn).2)
    have hcleNat : large.card ≤ S.card := card_le_card (filter_subset _ S)
    have hcle : (large.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcleNat
    have hc : (large.card : ℝ) ≤ N := hcle.trans hcard
    rw [sum_const,nsmul_eq_mul] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hNp.le)).trans_eq (mul_inv_cancel₀ hNp.ne'))
  have he := sum_filter_add_sum_filter_not S (fun n : ℤ => |(n : ℝ)| ≤ N) (fun n : ℤ => |(n : ℝ)|⁻¹)
  change (∑ n ∈ small, |(n : ℝ)|⁻¹)+(∑ n ∈ large, |(n : ℝ)|⁻¹) = _ at he
  linarith only [he,hsmall,hlarge]

/-- A source interval diameter gives the required actual cardinal bound. -/
theorem k4_sum_inv_abs_le_log (S : Finset ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ n ∈ S, ∀ m ∈ S, |(n : ℝ)-m| ≤ D) :
    ∑ n ∈ S, |(n : ℝ)|⁻¹ ≤ 3+2*Real.log (⌈D+1⌉₊ : ℝ) := by
  have hN : 0 < ⌈D+1⌉₊ := Nat.ceil_pos.mpr (by linarith only [hD])
  have hc : (S.card : ℝ) ≤ ⌈D+1⌉₊ :=
    (Counting.card_int_finset_le_of_diameter S hD hd).trans (Nat.le_ceil _)
  have hh := k4_sum_inv_abs_le_harmonic S hN hc
  have hl := harmonic_le_one_add_log ⌈D+1⌉₊
  nlinarith only [hh,hl]

end WaveTurbulence.MoleProp
