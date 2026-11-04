/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.ShiftedGevreyEnvelope
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! # Uniform control of all Wick derivative shifts

The number of frozen energies may grow with the order. The factorial
trace cost is kept explicit so each trace's lattice-power gain can pay it.
-/

public section
namespace WaveTurbulence.RegAsymp

/-- The binomial bound separates a derivative order and a trace shift. -/
theorem even_factorial_add_le (k s : ℕ) :
    (2*(k+s)).factorial ≤ 4^(k+s)*(2*k).factorial*(2*s).factorial := by
  calc
    _ = (2*k+2*s).choose (2*s)*(2*k).factorial*(2*s).factorial := by
      rw [Nat.add_choose_mul_factorial_mul_factorial]
      congr 1 <;> omega
    _ ≤ 2^(2*k+2*s)*(2*k).factorial*(2*s).factorial :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _))
    _ = _ := by
      rw [show 2*k+2*s = 2*(k+s) by omega,pow_mul]
      norm_num

/-- Every shifted summand has only an explicit trace factorial loss. -/
theorem shifted_gevrey_ratio_uniform_le {A : ℝ} (hA : 0 ≤ A) (s k : ℕ) :
    A^(k+s)*((2*(k+s)).factorial:ℝ)/(4*k).factorial ≤
      ((4*A)^s*(2*s).factorial)*((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial) := by
  have hf : ((2*(k+s)).factorial:ℝ) ≤ (4:ℝ)^(k+s)*(2*k).factorial*(2*s).factorial := by
    exact_mod_cast even_factorial_add_le k s
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity)).trans_eq
  rw [pow_add,mul_pow,mul_pow,pow_add]
  ring

/-- Quantitative mass bound uniform in the growing trace shift. -/
theorem tsum_shifted_gevrey_ratio_le {A : ℝ} (hA : 0 ≤ A) (s : ℕ) :
    (∑' k : ℕ, A^(k+s)*((2*(k+s)).factorial:ℝ)/(4*k).factorial) ≤
      ((4*A)^s*(2*s).factorial)*
        (∑' k : ℕ, (4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial) := by
  rw [← tsum_mul_left]
  exact (summable_shifted_gevrey_ratio A hA s).tsum_le_tsum
    (fun k => shifted_gevrey_ratio_uniform_le hA s k)
    ((summable_gevrey_ratio (4*A) (by positivity)).mul_left _)

end WaveTurbulence.RegAsymp
