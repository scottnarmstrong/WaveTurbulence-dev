/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.FourthDerivative
public import WaveTurbulence.Foundations.NumberTheory.DerivativeTowerShift
public import WaveTurbulence.Foundations.NumberTheory.AProcessDerivativeStep
import Mathlib.Tactic

/-!
# Fifth-derivative test by an actual A-step

A shifted fifth-order derivative tower supplies the fourth-derivative test
on the exact overlap. Both resulting power terms survive the optimization.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Continuous fifth-derivative test, with actual derivative values on the
sample interval including its two right-hand endpoint units. -/
theorem van_der_corput_fifth_derivative_tower (F : ℕ → ℝ → ℝ) (a : ℤ) (N : ℕ)
    {lam c : ℝ} (hlam : 0 < lam) (hc : 1 ≤ c)
    (hd : ∀ r : ℕ, r < 5 → ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      HasDerivAt (F r) (F (r+1) x) x)
    (hb : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2), F 5 x ∈ Set.Icc lam (c*lam)) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (F 0 n)‖ ≤
      8192*Real.sqrt c*((N:ℝ)*lam^((1:ℝ)/30)+(N:ℝ)^((7:ℝ)/8)*lam^(-((1:ℝ)/30))) := by
  have hsqrt : 1 ≤ Real.sqrt c := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hc
  have hD : 1 ≤ 256*Real.sqrt c := by linarith only [hsqrt]
  have hshift (h : ℕ) (hh : 0 < h) (hhN : h ≤ N) :
      ‖∑ n ∈ (Finset.Ioc a (a+N)).filter (fun n => n+(h:ℤ) ∈ Finset.Ioc a (a+N)),
        expPhase (F 0 ((n+(h:ℤ):ℤ):ℝ)-F 0 n)‖ ≤
          (256*Real.sqrt c)*((N:ℝ)*(lam*(h:ℝ))^((1:ℝ)/14)+
            (N:ℝ)^((3:ℝ)/4)*(lam*(h:ℝ))^(-((1:ℝ)/14))) := by
    have hhR : 0 < (h:ℝ) := by exact_mod_cast hh
    have hG := derivative_tower_positive_shift F 4 a N h hh hhN hd hb
    have ht := van_der_corput_fourth_derivative_tower (fun r => phaseDifference (F r) (h:ℝ))
      a (N-h) (mul_pos hlam hhR) hc hG.1 hG.2
    have hMN : ((N-h:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.sub_le N h
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (N-h)) hMN (by norm_num : (0:ℝ) ≤ 3/4)
    rw [int_window_positive_shift_filter a N h hhN]
    calc
      _ = ‖∑ n ∈ Finset.Ioc a (a+((N-h:ℕ):ℤ)), expPhase (phaseDifference (F 0) (h:ℝ) n)‖ := by
        simp only [phaseDifference,Int.cast_add,Int.cast_natCast]
      _ ≤ (256*Real.sqrt c)*(((N-h:ℕ):ℝ)*(lam*(h:ℝ))^((1:ℝ)/14)+
          ((N-h:ℕ):ℝ)^((3:ℝ)/4)*(lam*(h:ℝ))^(-((1:ℝ)/14))) := ht
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hMN (by positivity))
        (mul_le_mul_of_nonneg_right hpow (by positivity))) (by positivity)
  have ht := weyl_vdC_norm_le_derivative_step (fun n : ℤ => F 0 n) a N hlam hD
    (by norm_num : (0:ℝ) < 1/14) (by norm_num : (1:ℝ)/14 < 1)
    (by norm_num : (0:ℝ) ≤ 3/4) (fun h hh hhn => by simpa only using! hshift h hh hhn)
  have he1 : ((1:ℝ)/14)/(2*(1/14)+2) = 1/30 := by norm_num
  have he2 : (((3:ℝ)/4)+1)/2 = 7/8 := by norm_num
  rw [he1,he2] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  norm_num [div_eq_mul_inv]
  nlinarith only [Real.sqrt_nonneg c]

/-- Negative fifth-derivative variant via exact conjugation. -/
theorem van_der_corput_fifth_derivative_tower_of_neg (F : ℕ → ℝ → ℝ) (a : ℤ) (N : ℕ)
    {lam c : ℝ} (hlam : 0 < lam) (hc : 1 ≤ c)
    (hd : ∀ r : ℕ, r < 5 → ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      HasDerivAt (F r) (F (r+1) x) x)
    (hb : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2), F 5 x ∈ Set.Icc (-c*lam) (-lam)) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (F 0 n)‖ ≤
      8192*Real.sqrt c*((N:ℝ)*lam^((1:ℝ)/30)+(N:ℝ)^((7:ℝ)/8)*lam^(-((1:ℝ)/30))) := by
  have he := van_der_corput_fifth_derivative_tower (fun r x => -F r x) a N hlam hc
    (fun r hr x hx => (hd r hr x hx).neg) (fun x hx => by
      have hh := hb x hx
      constructor <;> linarith only [hh.1,hh.2])
  rw [norm_sum_expPhase_neg] at he
  exact he

end WaveTurbulence.NumberTheory
