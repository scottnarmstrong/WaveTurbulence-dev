/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.ThirdDifference
public import WaveTurbulence.Foundations.NumberTheory.FiniteDifferenceMeanValue
public import WaveTurbulence.Foundations.NumberTheory.DerivativeTests
import Mathlib.Tactic

/-!
# The third-derivative test from actual continuous derivatives

The generalized finite-difference mean-value theorem transfers a real
three-step derivative tower to the proved third finite-difference test.
The available derivative interval includes the actual endpoint samples.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Continuous third-derivative test on an integer window. The two extra
units on the right supply all actual third finite-difference samples. -/
theorem van_der_corput_third_derivative_tower (F : ℕ → ℝ → ℝ) (a : ℤ) (N : ℕ)
    {lam c : ℝ} (hlam : 0 < lam) (hc : 1 ≤ c)
    (hd : ∀ r : ℕ, r < 3 → ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      HasDerivAt (F r) (F (r+1) x) x)
    (hb : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2), F 3 x ∈ Set.Icc lam (c*lam)) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (F 0 n)‖ ≤
      12*Real.sqrt c*((N:ℝ)*lam^((1:ℝ)/6)+(N:ℝ)^((1:ℝ)/2)*lam^(-((1:ℝ)/6))) := by
  have hfinite (n : ℤ) (hn1 : a < n) (hn2 : n < a+(N:ℤ)) :
      forwardDifference 3 (F 0) n ∈ Set.Icc lam (c*lam) := by
    have hlo : (a:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hn1)
    have hhi : (n:ℝ)+3 ≤ (a:ℝ)+N+2 := by
      have hi : n+1 ≤ a+(N:ℤ) := Int.add_one_le_iff.mpr hn2
      have hiR : (n:ℝ)+1 ≤ (a:ℝ)+N := by exact_mod_cast hi
      linarith only [hiR]
    apply forwardDifference_mem_Icc F 3 n
    · intro r hr x hx
      apply hd r hr x
      norm_num only [Nat.cast_ofNat] at hx
      constructor <;> linarith only [hlo,hhi,hx.1,hx.2]
    · intro x hx
      apply hb x
      norm_num only [Nat.cast_ofNat] at hx
      constructor <;> linarith only [hlo,hhi,hx.1,hx.2]
  apply van_der_corput_third_difference (fun n : ℤ => F 0 n) a N lam c hlam hc
  · intro n hn1 hn2
    have he := (hfinite n hn1 hn2).1
    rw [forwardDifference_three] at he
    simpa only [Int.cast_add,Int.cast_ofNat,Int.cast_one] using! he
  · intro n hn1 hn2
    have he := (hfinite n hn1 hn2).2
    rw [forwardDifference_three] at he
    simpa only [Int.cast_add,Int.cast_ofNat,Int.cast_one] using! he

/-- The negative third-derivative variant, from exact character conjugation. -/
theorem van_der_corput_third_derivative_tower_of_neg (F : ℕ → ℝ → ℝ) (a : ℤ) (N : ℕ)
    {lam c : ℝ} (hlam : 0 < lam) (hc : 1 ≤ c)
    (hd : ∀ r : ℕ, r < 3 → ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      HasDerivAt (F r) (F (r+1) x) x)
    (hb : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2), F 3 x ∈ Set.Icc (-c*lam) (-lam)) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (F 0 n)‖ ≤
      12*Real.sqrt c*((N:ℝ)*lam^((1:ℝ)/6)+(N:ℝ)^((1:ℝ)/2)*lam^(-((1:ℝ)/6))) := by
  have he := van_der_corput_third_derivative_tower (fun r x => -F r x) a N hlam hc
    (fun r hr x hx => (hd r hr x hx).neg) (fun x hx => by
      have hh := hb x hx
      constructor <;> linarith only [hh.1,hh.2])
  rw [norm_sum_expPhase_neg] at he
  exact he

end WaveTurbulence.NumberTheory
