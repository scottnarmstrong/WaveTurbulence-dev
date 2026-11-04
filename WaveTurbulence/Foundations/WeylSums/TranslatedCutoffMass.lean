/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearTensor

/-! # Uniform lattice mass of a real translated cutoff -/

public section
open Finset
namespace WaveTurbulence.WeylSums

theorem summable_translated_chi0 {L : ℝ} (hL : 0 < L) (a : ℝ) :
    Summable (fun n : ℤ => Fourier.chi0 ((n : ℝ)/L-a)) :=
  summable_of_hasFiniteSupport (finite_scalar_cutoff hL a)

/-- A translated fixed cutoff has lattice mass at most `5L`, uniformly in
its arbitrary real center, for every real scale `L≥1`. -/
theorem tsum_translated_chi0_le {L : ℝ} (hL : 1 ≤ L) (a : ℝ) :
    (∑' n : ℤ, Fourier.chi0 ((n : ℝ)/L-a)) ≤ 5*L := by
  classical
  have hLp : 0 < L := by linarith
  let lo := ⌊L*(a-1)⌋
  let hi := ⌈L*(a+1)⌉
  have hfinite : (∑' n : ℤ, Fourier.chi0 ((n : ℝ)/L-a)) =
      ∑ n ∈ Icc lo hi, Fourier.chi0 ((n : ℝ)/L-a) := by
    apply tsum_eq_sum
    intro n hn
    by_contra hz
    have ha : |(n : ℝ)/L-a| < 1 := by
      by_contra hh
      exact hz (Fourier.chi0_eq_zero (not_lt.mp hh))
    obtain ⟨hl,hu⟩ := abs_lt.mp ha
    apply hn
    apply mem_Icc.mpr
    constructor
    · apply Int.floor_le_iff.mpr
      have hh := (le_div_iff₀ hLp).mp (show a-1 ≤ (n : ℝ)/L by linarith)
      exact_mod_cast (by linarith : L*(a-1) < (n : ℝ)+1)
    · apply Int.le_ceil_iff.mpr
      have hh := (div_le_iff₀ hLp).mp (show (n : ℝ)/L ≤ a+1 by linarith)
      exact_mod_cast (by linarith : (n : ℝ)-1 < L*(a+1))
  have hlo : (lo : ℝ) ≤ L*(a-1) := Int.floor_le _
  have hhi : L*(a+1) ≤ (hi : ℝ) := Int.le_ceil _
  have hlohi : lo ≤ hi+1 := by
    exact_mod_cast (by push_cast; nlinarith only [hlo,hhi,hL] : (lo : ℝ) ≤ ((hi+1 : ℤ) : ℝ))
  have hcard : ((Icc lo hi).card : ℝ) = (hi : ℝ)+1-lo := by
    exact_mod_cast Int.card_Icc_of_le lo hi hlohi
  have hceil : (hi : ℝ) < L*(a+1)+1 := Int.ceil_lt_add_one _
  have hfloor : L*(a-1) < (lo : ℝ)+1 := Int.lt_floor_add_one _
  rw [hfinite]
  calc
    _ ≤ ∑ _n ∈ Icc lo hi, (1 : ℝ) := sum_le_sum (fun n hn => Fourier.chi0_le_one _)
    _ = ((Icc lo hi).card : ℝ) := by simp
    _ ≤ 5*L := by rw [hcard]; nlinarith only [hceil,hfloor,hL]

end WaveTurbulence.WeylSums
