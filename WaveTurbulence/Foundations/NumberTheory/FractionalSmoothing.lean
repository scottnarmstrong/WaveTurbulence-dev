/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.SmoothingFourier
public import WaveTurbulence.Foundations.NumberTheory.FractionalPowerSums
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Fourier smoothing for a general fractional frequency exponent

A distinct conditional helper for the NT-EXPSUM exponent-pair transfer.
The frequency estimate is an explicit input for an arbitrary finite phase
family; no circle estimate or improved exponent pair is asserted here.
-/

public section

namespace WaveTurbulence.NumberTheory

private theorem smoothing_rpow_low {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {A kappa : ℝ} {H n : ℕ} (hH : 0 < H) (hn : 0 < n)
    (hb : ‖∑ i ∈ s, expPhase ((n:ℝ)*f i)‖ ≤ A*(n:ℝ)^kappa) :
    ‖expPhase ((n:ℝ)*(1/H))-1‖*‖∑ i ∈ s, expPhase ((n:ℝ)*f i)‖/(n:ℝ)^2 ≤
      (2*Real.pi*A/H)*(n:ℝ)^(kappa-1) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hHR : 0 < (H:ℝ) := by exact_mod_cast hH
  have hc := norm_expPhase_sub_one_le ((n:ℝ)*(1/H))
  rw [abs_of_pos (mul_pos hnR (one_div_pos.mpr hHR))] at hc
  have hp := mul_le_mul hc hb (norm_nonneg _) (by positivity : 0 ≤ 2*Real.pi*((n:ℝ)*(1/H)))
  calc
    _ ≤ (2*Real.pi*((n:ℝ)*(1/H)))*(A*(n:ℝ)^kappa)/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right hp (sq_nonneg _)
    _ = _ := by rw [Real.rpow_sub_one hnR.ne']; field_simp

private theorem smoothing_rpow_high {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {A kappa : ℝ} {H n : ℕ} (hn : 0 < n)
    (hb : ‖∑ i ∈ s, expPhase ((n:ℝ)*f i)‖ ≤ A*(n:ℝ)^kappa) :
    ‖expPhase ((n:ℝ)*(1/H))-1‖*‖∑ i ∈ s, expPhase ((n:ℝ)*f i)‖/(n:ℝ)^2 ≤
      (2*A)*(n:ℝ)^(kappa-2) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hp := mul_le_mul (norm_expPhase_sub_one_le_two ((n:ℝ)*(1/H))) hb (norm_nonneg _) zero_le_two
  calc
    _ ≤ 2*(A*(n:ℝ)^kappa)/(n:ℝ)^2 := div_le_div_of_nonneg_right hp (sq_nonneg _)
    _ = _ := by rw [Real.rpow_sub hnR,Real.rpow_two]; ring

/-- General fractional-frequency bound for the absolutely convergent
smoothing majorant. This is a Fourier inequality, not an exponent-pair claim. -/
theorem tsum_smoothing_majorant_le_of_rpow_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {A kappa : ℝ} (hA : 0 ≤ A) (hk : 0 < kappa) (hk1 : kappa < 1)
    {H : ℕ} (hH : 0 < H)
    (hb : ∀ n : ℕ, 0 < n → ‖∑ i ∈ s, expPhase ((n:ℝ)*f i)‖ ≤ A*(n:ℝ)^kappa) :
    (∑' n : ℕ, ‖expPhase ((n:ℝ)*(1/H))-1‖*
      ‖∑ i ∈ s, expPhase ((n:ℝ)*f i)‖/(n:ℝ)^2) ≤
      (2*Real.pi/kappa+2/(1-kappa))*A*(H:ℝ)^(kappa-1) := by
  let w : ℕ → ℝ := fun n => ‖expPhase ((n:ℝ)*(1/H))-1‖*
    ‖∑ i ∈ s, expPhase ((n:ℝ)*f i)‖/(n:ℝ)^2
  have hHR : 0 < (H:ℝ) := by exact_mod_cast hH
  have hhead : (∑ n ∈ Finset.range (H+1), w n) ≤
      (2*Real.pi*A/H)*((H:ℝ)^kappa/kappa) := by
    rw [Finset.sum_range_succ']
    have hw0 : w 0 = 0 := by simp only [w,Nat.cast_zero,zero_mul,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,div_zero]
    rw [hw0,add_zero]
    calc
      _ ≤ ∑ i ∈ Finset.range H, (2*Real.pi*A/H)*((i+1:ℕ):ℝ)^(kappa-1) :=
        Finset.sum_le_sum (fun i _ => smoothing_rpow_low s f hH (Nat.zero_lt_succ i) (hb _ (Nat.zero_lt_succ i)))
      _ = (2*Real.pi*A/H)*∑ i ∈ Finset.range H, ((i+1:ℕ):ℝ)^(kappa-1) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_rpow_sub_one_le hk hk1.le H) (by positivity)
  have htail : (∑' i : ℕ, w (i+(H+1))) ≤ (2*A)*((H:ℝ)^(kappa-1)/(1-kappa)) := by
    have hpoint (i : ℕ) : w (i+(H+1)) ≤ (2*A)*((i+H+1:ℕ):ℝ)^(kappa-2) := by
      have hn : 0 < i+(H+1) := by omega
      simpa only [Nat.add_assoc] using smoothing_rpow_high s f (H := H) hn (hb _ hn)
    calc
      _ ≤ ∑' i : ℕ, (2*A)*((i+H+1:ℕ):ℝ)^(kappa-2) := by
        apply Summable.tsum_le_tsum hpoint
        · exact (summable_smoothing_majorant s f (1/H)).comp_injective (fun i j h => Nat.add_right_cancel h)
        · exact (summable_rpow_sub_two_tail hk1 H).mul_left _
      _ = (2*A)*∑' i : ℕ, ((i+H+1:ℕ):ℝ)^(kappa-2) := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_rpow_sub_two_tail_le hk1 hH) (by positivity)
  have hsplit := (summable_smoothing_majorant s f (1/H)).sum_add_tsum_nat_add (H+1)
  change (∑ n ∈ Finset.range (H+1), w n)+(∑' i : ℕ, w (i+(H+1))) = _ at hsplit
  rw [← hsplit]
  calc
    _ ≤ (2*Real.pi*A/H)*((H:ℝ)^kappa/kappa)+(2*A)*((H:ℝ)^(kappa-1)/(1-kappa)) := add_le_add hhead htail
    _ = _ := by rw [Real.rpow_sub_one hHR.ne']; ring

private theorem fractional_smoothing_scale {C A H kappa : ℝ} (hH : 0 < H) :
    ((2*C)*A*H^(kappa-1))/(2*(1/H)*Real.pi^2) = (C/Real.pi^2)*A*H^kappa := by
  rw [Real.rpow_sub_one hH.ne']
  field_simp

/-- Summed sawtooth cancellation from a general frequency exponent in `(0,1)`.
The explicit frequency-bound hypothesis is discharged separately in applications. -/
theorem abs_sum_sawtooth_le_of_rpow_exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {A kappa : ℝ} (hA : 0 ≤ A) (hk : 0 < kappa) (hk1 : kappa < 1)
    {H : ℕ} (hH : 0 < H)
    (hb : ∀ n : ℕ, 0 < n → ‖∑ i ∈ s, expPhase ((n:ℝ)*f i)‖ ≤ A*(n:ℝ)^kappa) :
    |∑ i ∈ s, sawtooth (f i)| ≤ (s.card:ℝ)/(2*H)+
      ((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*A*(H:ℝ)^kappa := by
  have hHR : 0 < (H:ℝ) := by exact_mod_cast hH
  have hs := abs_sum_sawtooth_le_smoothing_series s f (one_div_pos.mpr hHR)
  have hm := tsum_smoothing_majorant_le_of_rpow_bound s f hA hk hk1 hH hb
  have hd := div_le_div_of_nonneg_right hm (by positivity : 0 ≤ 2*(1/(H:ℝ))*Real.pi^2)
  have hhead : (s.card:ℝ)*((1/(H:ℝ))/2) = (s.card:ℝ)/(2*H) := by ring
  rw [hhead] at hs
  apply hs.trans (add_le_add le_rfl ?_)
  apply hd.trans_eq
  rw [show 2*Real.pi/kappa+2/(1-kappa) = 2*(Real.pi/kappa+1/(1-kappa)) by ring]
  exact fractional_smoothing_scale hHR

end WaveTurbulence.NumberTheory
