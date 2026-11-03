/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.AnnulusDiscrepancy

/-! # A uniform planar squared-radius shell estimate -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- Combining the two-thirds discrepancy with the elementary local annulus
bound gives the coarser `O(W+L)` estimate, uniformly in both centers. This
version retains the radial parameters, with `W=Q*ρ ≥ 1`. -/
theorem card_annulus_coarse_le (s : Finset (Fin 2 → ℤ))
    (c : Mom 2) (b : Fin 2 → ℝ) {Q ρ R : ℝ}
    (hQ : 2 ≤ Q) (hρ : 0 < ρ) (hρQ : ρ ≤ Q/4)
    (hW : 1 ≤ Q*ρ) (hR : 0 ≤ R)
    (hbox : ∀ n ∈ s, ∀ i, |(n i : ℝ)-b i| ≤ R)
    (hann : ∀ n ∈ s, |‖latticePoint 1 n-c‖-Q| ≤ ρ) :
    (s.card : ℝ) ≤ (6*Real.pi+1284002)*(Q*ρ+R) := by
  let W := Q*ρ
  let r := Q^((1 : ℝ)/3)
  have hQp : 0 < Q := by linarith only [hQ]
  have hr : 0 < r := Real.rpow_pos_of_pos hQp _
  have hr3 : r^3 = Q := by
    simpa only [r,one_div,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hQp.le (show (3 : ℕ) ≠ 0 by decide)
  have hr2 : Q^((2 : ℝ)/3) = r^2 := by
    dsimp only [r]
    rw [← Real.rpow_natCast,← Real.rpow_mul hQp.le]
    congr 1
    norm_num
  have hWp : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hWsqrt : Real.sqrt W ≤ W := (Real.sqrt_le_iff).mpr ⟨hWp.le,by nlinarith only [hW]⟩
  by_cases hs : r^2 ≤ W+R
  · have hb := Counting.card_annulus_le_two_thirds s c hQ hρ hρQ hann
    rw [hr2] at hb
    change (s.card : ℝ) ≤ 6*Real.pi*W+4002*r^2 at hb
    have hh := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4002)
    have hp := mul_nonneg Real.pi_pos.le hR
    nlinarith only [hb,hh,hp,hR,hWp]
  · have hWr : W ≤ r^2 := (le_add_of_nonneg_right hR).trans (le_of_not_ge hs)
    have hsqr : Real.sqrt W ≤ r := (Real.sqrt_le_iff).mpr ⟨hr.le,hWr⟩
    have hterm1 : R*ρ*Real.sqrt W ≤ R := by
      have hnum : W*Real.sqrt W ≤ Q := by
        rw [← hr3]
        calc
          _ ≤ r^2*r := mul_le_mul hWr hsqr (Real.sqrt_nonneg _) (sq_nonneg _)
          _ = r^3 := by ring
      have hρsqrt : ρ*Real.sqrt W ≤ 1 := by
        have hmul : Q*(ρ*Real.sqrt W) ≤ Q := by simpa only [W,mul_assoc] using hnum
        exact (mul_le_mul_iff_right₀ hQp).mp (by simpa only [mul_comm,mul_one] using hmul)
      simpa only [mul_assoc,mul_one] using mul_le_mul_of_nonneg_left hρsqrt hR
    have hterm2 : R/r*Real.sqrt W ≤ R := by
      apply (mul_le_mul_iff_right₀ hr).mp
      calc
        r*(R/r*Real.sqrt W) = R*Real.sqrt W := by field_simp
        _ ≤ r*R := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsqr hR
    have hb := Counting.card_annulus_square_le s hQp hρ.le
      (by linarith only [hρQ,hQp]) hW hR
      (fun n hn => ⟨hbox n hn 0,hbox n hn 1⟩)
      (by
        intro n hn
        rw [← Counting.norm_latticePoint_one_sub_eq_sqrt]
        exact hann n hn)
    change (s.card : ℝ) ≤ 640000*(1+R*ρ+R/r)*Real.sqrt W at hb
    have hpoly : 640000*(1+R*ρ+R/r)*Real.sqrt W ≤ 640000*(W+2*R) := by
      nlinarith only [hWsqrt,hterm1,hterm2]
    have hp : 0 ≤ Real.pi*(W+R) := mul_nonneg Real.pi_pos.le (add_nonneg hWp.le hR)
    have hh : 0 ≤ W+R := add_nonneg hWp.le hR
    nlinarith only [hb,hpoly,hp,hh,hWp]

end WaveTurbulence.CountLemmas
