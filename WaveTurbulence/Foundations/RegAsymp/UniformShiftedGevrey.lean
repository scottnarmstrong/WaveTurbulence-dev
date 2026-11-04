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
open scoped ENNReal

/-- The binomial bound separates a derivative order and a trace shift. -/
theorem even_factorial_add_le (k s : ℕ) :
    (2*(k+s)).factorial ≤ 4^(k+s)*(2*k).factorial*(2*s).factorial := by
  calc
    _ = (2*k+2*s).choose (2*s)*(2*k).factorial*(2*s).factorial := by
      rw [Nat.add_choose_mul_factorial_mul_factorial]
      congr 1
      omega
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

/-- The quantitative shift bound in the actual ENNReal mass convention. -/
theorem tsum_shifted_gevrey_ratio_ennreal_le {A : ℝ} (hA : 0 ≤ A) (s : ℕ) :
    (∑' k : ℕ, ENNReal.ofReal (A^(k+s)*((2*(k+s)).factorial:ℝ)/(4*k).factorial)) ≤
      ENNReal.ofReal ((4*A)^s*(2*s).factorial)*
        (∑' k : ℕ, ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) := by
  have h4A : 0 ≤ 4*A := by positivity
  calc
    _ = ENNReal.ofReal (∑' k : ℕ, A^(k+s)*((2*(k+s)).factorial:ℝ)/(4*k).factorial) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (summable_shifted_gevrey_ratio A hA s)).symm
    _ ≤ ENNReal.ofReal (((4*A)^s*(2*s).factorial)*
        (∑' k : ℕ, (4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) :=
      ENNReal.ofReal_le_ofReal (tsum_shifted_gevrey_ratio_le hA s)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
        (summable_gevrey_ratio (4*A) h4A)]

/-- All shifts up to r share one explicit factorial budget. -/
theorem tsum_shifted_gevrey_ratio_ennreal_le_of_le {A : ℝ} (hA : 0 ≤ A) {s r : ℕ} (hsr : s ≤ r) :
    (∑' k : ℕ, ENNReal.ofReal (A^(k+s)*((2*(k+s)).factorial:ℝ)/(4*k).factorial)) ≤
      ENNReal.ofReal ((max 1 (4*A))^r*(2*r).factorial)*
        (∑' k : ℕ, ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) := by
  apply (tsum_shifted_gevrey_ratio_ennreal_le hA s).trans
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  have hp : (4*A)^s ≤ (max 1 (4*A))^r :=
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) s).trans
      (pow_le_pow_right₀ (le_max_left _ _) hsr)
  have hf : ((2*s).factorial:ℝ) ≤ (2*r).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.mul_le_mul_left 2 hsr)
  exact mul_le_mul hp hf (by positivity) (by positivity)

end WaveTurbulence.RegAsymp
