/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.ThirdDifference
public import WaveTurbulence.Foundations.NumberTheory.FractionalPowerSums
import Mathlib.Tactic

/-!
# A-process with both derivative-test power terms

The higher derivative test has a positive and a negative power of the
shift length. Both terms are retained in the exact Weyl inequality. The
negative powers are summed by the proved fractional integral bound.
-/

public section

namespace WaveTurbulence.NumberTheory

open Finset

/-- Quantitative A-step for actual positive-shift sums bounded by two
opposite powers. Negative shifts follow from exact conjugation symmetry. -/
theorem weyl_vdC_sq_le_two_power_shifts (f : ℤ → ℝ) (a : ℤ) {N H : ℕ}
    (hH : 0 < H) (hHN : H ≤ N) {A B alpha : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hshift : ∀ h : ℕ, 0 < h → h ≤ H →
      ‖∑ n ∈ (Ioc a (a+N)).filter (fun n => n+(h:ℤ) ∈ Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤ A*(h:ℝ)^alpha+B*(h:ℝ)^(-alpha)) :
    ‖∑ n ∈ Ioc a (a+N), expPhase (f n)‖^2 ≤
      2*(N:ℝ)^2/H+4*(N:ℝ)*A*(H:ℝ)^alpha+
        (4*(N:ℝ)*B/(1-alpha))*(H:ℝ)^(-alpha) := by
  classical
  let G : ℤ → ℂ := fun h => ∑ n ∈ (Ioc a (a+N)).filter (fun n => n+h ∈ Ioc a (a+N)),
    expPhase (f (n+h)-f n)
  have hzero : ‖G 0‖ = (N:ℝ) := by
    have hfilter : (Ioc a (a+N)).filter (fun n : ℤ => n+0 ∈ Ioc a (a+N)) = Ioc a (a+N) := by
      ext n
      simp only [Finset.mem_filter,add_zero,and_self]
    have hc : (Ioc a (a+N)).card = N := by rw [Int.card_Ioc]; omega
    dsimp only [G]
    rw [hfilter]
    simp only [add_zero,sub_self,expPhase_zero,Finset.sum_const,nsmul_eq_mul,mul_one,
      Complex.norm_natCast,hc]
  have hneg (h : ℤ) : ‖G (-h)‖ = ‖G h‖ := norm_shifted_exp_sum_neg f a N h
  have hsym : (∑ h ∈ Icc (-(H:ℤ)) H, ‖G h‖) =
      (N:ℝ)+2*(∑ i ∈ range H, ‖G ((i:ℤ)+1)‖) := by
    rw [sum_symmetric_integer_interval,hzero]
    simp_rw [hneg]
    rw [Finset.sum_add_distrib]
    ring
  have hpos : (∑ i ∈ range H, ((i+1:ℕ):ℝ)^alpha) ≤ (H:ℝ)*(H:ℝ)^alpha := by
    calc
      _ ≤ ∑ _i ∈ range H, (H:ℝ)^alpha := Finset.sum_le_sum (fun i hi =>
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)) ha.le)
      _ = _ := by rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hinv : (∑ i ∈ range H, ((i+1:ℕ):ℝ)^(-alpha)) ≤ (H:ℝ)^(1-alpha)/(1-alpha) := by
    have he : (1-alpha)-1 = -alpha := by ring
    simpa only [he] using sum_rpow_sub_one_le (sub_pos.mpr ha1)
      (by linarith only [ha] : 1-alpha ≤ 1) H
  have hlocal : (∑ i ∈ range H, ‖G ((i:ℤ)+1)‖) ≤
      A*((H:ℝ)*(H:ℝ)^alpha)+B*((H:ℝ)^(1-alpha)/(1-alpha)) := by
    calc
      _ ≤ ∑ i ∈ range H, (A*((i+1:ℕ):ℝ)^alpha+B*((i+1:ℕ):ℝ)^(-alpha)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hb := hshift (i+1) (by omega) (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
        simpa only [G,Nat.cast_add,Nat.cast_one,Int.natCast_add,Int.natCast_one] using hb
      _ = A*(∑ i ∈ range H, ((i+1:ℕ):ℝ)^alpha)+B*(∑ i ∈ range H, ((i+1:ℕ):ℝ)^(-alpha)) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hpos hA) (mul_le_mul_of_nonneg_left hinv hB)
  have hsum : (∑ h ∈ Icc (-(H:ℤ)) H, ‖G h‖) ≤
      (N:ℝ)+2*(A*((H:ℝ)*(H:ℝ)^alpha)+B*((H:ℝ)^(1-alpha)/(1-alpha))) := by
    rw [hsym]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlocal (by norm_num))
  have hHR : 0 < (H:ℝ) := by exact_mod_cast hH
  have hHNR : (H:ℝ) ≤ N := by exact_mod_cast hHN
  have hfront : (N+H:ℝ)/(H+1) ≤ (2*(N:ℝ))/H := by
    calc
      _ ≤ (2*(N:ℝ))/(H+1) := div_le_div_of_nonneg_right (by linarith only [hHNR]) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hHR (by linarith only)
  have hp : (H:ℝ)^(1-alpha)/(H:ℝ) = (H:ℝ)^(-alpha) := by
    rw [← Real.rpow_sub_one hHR.ne' (1-alpha)]
    congr 1
    ring
  calc
    _ ≤ ((N+H:ℝ)/(H+1))*(∑ h ∈ Icc (-(H:ℤ)) H, ‖G h‖) := weyl_vdC_expSum f a N H
    _ ≤ ((N+H:ℝ)/(H+1))*((N:ℝ)+2*(A*((H:ℝ)*(H:ℝ)^alpha)+B*((H:ℝ)^(1-alpha)/(1-alpha)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((2*(N:ℝ))/H)*((N:ℝ)+2*(A*((H:ℝ)*(H:ℝ)^alpha)+B*((H:ℝ)^(1-alpha)/(1-alpha)))) :=
      mul_le_mul_of_nonneg_right hfront (by positivity)
    _ = 2*(N:ℝ)^2/H+4*(N:ℝ)*A*(H:ℝ)^alpha+
        (4*(N:ℝ)*B/(1-alpha))*((H:ℝ)^(1-alpha)/H) := by field_simp; ring
    _ = _ := by rw [hp]

end WaveTurbulence.NumberTheory
