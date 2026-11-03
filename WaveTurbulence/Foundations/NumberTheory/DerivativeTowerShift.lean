/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.PhaseDifferences
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Derivative towers on actual A-process overlap windows

A positive integer shift restricts the original window to its exact overlap.
The differenced tower has one fewer derivative, with last-derivative bounds
multiplied by the shift length. All evaluation points stay in the source
interval, including the two endpoint sample units used by derivative tests.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Signed derivative bounds transfer to the actual finite difference. -/
theorem phaseDifference_mem_Icc_of_deriv_mem_Icc {f g : ℝ → ℝ} {x h lo hi : ℝ}
    (hh : 0 < h) (hd : ∀ y ∈ Set.Icc x (x+h), HasDerivAt f (g y) y)
    (hb : ∀ y ∈ Set.Icc x (x+h), g y ∈ Set.Icc lo hi) :
    phaseDifference f h x ∈ Set.Icc (lo*h) (hi*h) := by
  obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope f g (by linarith only [hh])
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => hd y ⟨hy.1.le,hy.2.le⟩)
  have hy' : y ∈ Set.Icc x (x+h) := ⟨hy.1.le,hy.2.le⟩
  rw [show x+h-x = h by ring] at he
  have hval : phaseDifference f h x = g y*h := ((eq_div_iff hh.ne').mp he).symm
  rw [hval]
  exact ⟨mul_le_mul_of_nonneg_right (hb y hy').1 hh.le,
    mul_le_mul_of_nonneg_right (hb y hy').2 hh.le⟩

/-- Exact positive-shift overlap window for the Weyl correlation. -/
theorem int_window_positive_shift_filter (a : ℤ) (N h : ℕ) (hhN : h ≤ N) :
    (Finset.Ioc a (a+N)).filter (fun n => n+(h:ℤ) ∈ Finset.Ioc a (a+N)) =
      Finset.Ioc a (a+((N-h:ℕ):ℤ)) := by
  ext n
  simp only [Finset.mem_filter,Finset.mem_Ioc]
  rw [Nat.cast_sub hhN]
  omega

/-- A shifted tower has one fewer derivative on the exact integer overlap,
and its final derivative is between `lam*h` and `c*lam*h`. -/
theorem derivative_tower_positive_shift (F : ℕ → ℝ → ℝ) (k : ℕ) (a : ℤ) (N h : ℕ)
    {lam c : ℝ} (hh : 0 < h) (hhN : h ≤ N)
    (hd : ∀ r : ℕ, r < k+1 → ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      HasDerivAt (F r) (F (r+1) x) x)
    (hb : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2), F (k+1) x ∈ Set.Icc lam (c*lam)) :
    (∀ r : ℕ, r < k → ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+(N-h:ℕ)+2),
      HasDerivAt (phaseDifference (F r) (h:ℝ))
        (phaseDifference (F (r+1)) (h:ℝ) x) x) ∧
    (∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+(N-h:ℕ)+2),
      phaseDifference (F k) (h:ℝ) x ∈ Set.Icc (lam*(h:ℝ)) (c*(lam*(h:ℝ)))) := by
  have hhR : 0 < (h:ℝ) := by exact_mod_cast hh
  have hlen : ((N-h:ℕ):ℝ) = (N:ℝ)-(h:ℝ) := Nat.cast_sub hhN
  have hsource (x : ℝ) (hx : x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+(N-h:ℕ)+2))
      (y : ℝ) (hy : y ∈ Set.Icc x (x+(h:ℝ))) :
      y ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2) := by
    rw [hlen] at hx
    constructor <;> linarith only [hx.1,hx.2,hy.1,hy.2]
  constructor
  · intro r hr x hx
    apply phaseDifference_hasDerivAt
    · exact hd r (by omega) x (hsource x hx x ⟨le_rfl,by linarith only [hhR]⟩)
    · exact hd r (by omega) (x+h) (hsource x hx (x+h) ⟨by linarith only [hhR],le_rfl⟩)
  · intro x hx
    have he := phaseDifference_mem_Icc_of_deriv_mem_Icc hhR
      (fun y hy => hd k (by omega) y (hsource x hx y hy))
      (fun y hy => hb y (hsource x hx y hy))
    exact ⟨he.1,by nlinarith only [he.2]⟩

end WaveTurbulence.NumberTheory
