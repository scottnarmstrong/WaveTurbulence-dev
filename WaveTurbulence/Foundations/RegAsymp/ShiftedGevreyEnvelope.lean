/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.GevreyEnvelope

/-! # Fixed derivative shifts preserve the common Gevrey envelope

One-coordinate traces in the Wick exceptional-set estimate cost an
additional coefficient derivative. Every fixed shift remains summable
against the NT derivative denominator (4k)!.
-/

public section
namespace WaveTurbulence.RegAsymp

/-- The factorial gap still dominates k! once k is above twice the shift. -/
theorem shifted_gevrey_ratio_le {A : ℝ} (hA : 0 ≤ A) (s k : ℕ) (hk : 2*s ≤ k) :
    A^(k+s)*((2*(k+s)).factorial:ℝ)/(4*k).factorial ≤ A^s*(A^k/k.factorial) := by
  have hnat : (2*(k+s)).factorial*k.factorial ≤ (4*k).factorial :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add (2*(k+s)) k)).trans
      (Nat.factorial_le (by omega))
  have hcast : ((2*(k+s)).factorial:ℝ)*k.factorial ≤ (4*k).factorial := by exact_mod_cast hnat
  rw [pow_add]
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    _ = (A^k*A^s)*((2*(k+s)).factorial:ℝ) := rfl
    _ ≤ (A^k*A^s)*((4*k).factorial/k.factorial) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ (by positivity)).mpr hcast) (by positivity)
    _ = _ := by ring

/-- The common all-orders envelope also pays any fixed trace shift. -/
theorem summable_shifted_gevrey_ratio (A : ℝ) (hA : 0 ≤ A) (s : ℕ) :
    Summable (fun k : ℕ => A^(k+s)*((2*(k+s)).factorial:ℝ)/(4*k).factorial) := by
  apply ((Real.summable_pow_div_factorial A).mul_left (A^s)).of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_atTop.2 ⟨2*s,fun _ hk => hk⟩] with k hk
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact shifted_gevrey_ratio_le hA s k hk

end WaveTurbulence.RegAsymp
