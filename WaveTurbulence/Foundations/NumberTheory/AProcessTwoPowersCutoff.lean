/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.AProcessTwoPowers
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Real cutoffs with both A-process power terms

Rounding the cutoff to an actual integer preserves both positive and
negative powers, with absolute factors. This is the numerical induction
step for the higher derivative tests.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Choose `H=floor X` in the two-power A-step. Both signs of the phase
shift and the full negative-power error are retained. -/
theorem weyl_vdC_sq_le_two_power_real_cutoff (f : ℤ → ℝ) (a : ℤ) (N : ℕ)
    {A B alpha X : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hX1 : 1 ≤ X) (hXN : X ≤ (N:ℝ))
    (hshift : ∀ h : ℕ, 0 < h → h ≤ N →
      ‖∑ n ∈ (Finset.Ioc a (a+N)).filter (fun n => n+(h:ℤ) ∈ Finset.Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤ A*(h:ℝ)^alpha+B*(h:ℝ)^(-alpha)) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (f n)‖^2 ≤
      4*(N:ℝ)^2/X+4*(N:ℝ)*A*X^alpha+(8*(N:ℝ)*B/(1-alpha))*X^(-alpha) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hden : 0 < 1-alpha := sub_pos.mpr ha1
  let H : ℕ := ⌊X⌋₊
  have hH : 0 < H := Nat.floor_pos.mpr hX1
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hHp : 0 < (H:ℝ) := by exact_mod_cast hH
  have hHX : (H:ℝ) ≤ X := Nat.floor_le hXp.le
  have hXH : X/2 ≤ (H:ℝ) := by
    have hh := Nat.lt_floor_add_one X
    change X < (H:ℝ)+1 at hh
    linarith only [hh,hHR]
  have hHN : H ≤ N := by exact_mod_cast hHX.trans hXN
  have hb := weyl_vdC_sq_le_two_power_shifts f a hH hHN hA hB ha ha1
    (fun h hn hh => hshift h hn (hh.trans hHN))
  have hhead : 2*(N:ℝ)^2/H ≤ 4*(N:ℝ)^2/X := by
    calc
      _ ≤ (2*(N:ℝ)^2)/(X/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hXH
      _ = _ := by ring
  have hpos : 4*(N:ℝ)*A*(H:ℝ)^alpha ≤ 4*(N:ℝ)*A*X^alpha :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hHp.le hHX ha.le) (by positivity)
  have hneg : (H:ℝ)^(-alpha) ≤ 2*X^(-alpha) := by
    calc
      _ ≤ (X/2)^(-alpha) := Real.rpow_le_rpow_of_nonpos (by positivity) hXH (by linarith only [ha])
      _ = (2:ℝ)^alpha*X^(-alpha) := by
        rw [Real.div_rpow hXp.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ) ≤ 2) ha1.le) (Real.rpow_nonneg hXp.le _)
  have htail := mul_le_mul_of_nonneg_left hneg (by positivity : 0 ≤ 4*(N:ℝ)*B/(1-alpha))
  calc
    _ ≤ 2*(N:ℝ)^2/H+4*(N:ℝ)*A*(H:ℝ)^alpha+(4*(N:ℝ)*B/(1-alpha))*(H:ℝ)^(-alpha) := hb
    _ ≤ 4*(N:ℝ)^2/X+4*(N:ℝ)*A*X^alpha+(4*(N:ℝ)*B/(1-alpha))*(2*X^(-alpha)) :=
      add_le_add (add_le_add hhead hpos) htail
    _ = _ := by ring

end WaveTurbulence.NumberTheory
