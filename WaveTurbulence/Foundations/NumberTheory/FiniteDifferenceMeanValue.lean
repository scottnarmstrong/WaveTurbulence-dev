/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.PhaseDifferences
import Mathlib.Tactic

/-!
# Mean-value theorem for finite differences

An actual n-th unit finite difference equals an actual n-th derivative at
a point in the n-unit sample interval. The hypotheses are a derivative
tower on precisely that interval; no global extension is assumed.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The n-fold unit forward difference of a real phase. -/
@[expose] def forwardDifference : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, x => f x
  | n+1, f, x => forwardDifference n f (x+1)-forwardDifference n f x

/-- Differentiation commutes with unit finite differences at all actual
sample points. -/
theorem forwardDifference_hasDerivAt {f g : ℝ → ℝ} (n : ℕ) {x : ℝ}
    (hd : ∀ j : ℕ, j ≤ n → HasDerivAt f (g (x+j)) (x+j)) :
    HasDerivAt (forwardDifference n f) (forwardDifference n g x) x := by
  induction n generalizing x with
  | zero => simpa only [forwardDifference,Nat.cast_zero,add_zero] using hd 0 (by omega)
  | succ n ih =>
    have h0 := ih (x := x) (fun j hj => hd j (Nat.le_succ_of_le hj))
    have h1 := ih (x := x+1) (fun j hj => by
      have he : x+1+(j:ℝ) = x+((j+1:ℕ):ℝ) := by push_cast; ring
      rw [he]
      exact hd (j+1) (Nat.succ_le_succ hj))
    exact (h1.comp_add_const x 1).sub h0

/-- Generalized real mean-value theorem for actual unit finite differences.
The witness stays within the complete interval of sampled points. -/
theorem exists_forwardDifference_eq_derivative (F : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hd : ∀ r : ℕ, r < n → ∀ y ∈ Set.Icc x (x+n),
      HasDerivAt (F r) (F (r+1) y) y) :
    ∃ y ∈ Set.Icc x (x+n), forwardDifference n (F 0) x = F n y := by
  induction n generalizing F x with
  | zero => exact ⟨x,⟨le_rfl,by simp⟩,rfl⟩
  | succ n ih =>
    have hD (y : ℝ) (hy : y ∈ Set.Icc x (x+1)) :
        HasDerivAt (forwardDifference n (F 0)) (forwardDifference n (F 1) y) y := by
      apply forwardDifference_hasDerivAt
      intro j hj
      apply hd 0 (by omega)
      have hjR : (j:ℝ) ≤ n := by exact_mod_cast hj
      have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
      simp only [Nat.cast_add,Nat.cast_one]
      constructor <;> linarith only [hy.1,hy.2,hjR,hj0]
    have hc : ContinuousOn (forwardDifference n (F 0)) (Set.Icc x (x+1)) :=
      fun y hy => (hD y hy).continuousAt.continuousWithinAt
    obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope (forwardDifference n (F 0))
      (forwardDifference n (F 1)) (by linarith : x < x+1) hc
      (fun y hy => hD y ⟨hy.1.le,hy.2.le⟩)
    rw [show x+1-x = (1:ℝ) by ring,div_one] at he
    have hs : ∀ r : ℕ, r < n → ∀ z ∈ Set.Icc y (y+n),
        HasDerivAt (F (r+1)) (F ((r+1)+1) z) z := by
      intro r hr z hz
      apply hd (r+1) (by omega)
      simp only [Nat.cast_add,Nat.cast_one]
      constructor <;> linarith only [hy.1,hy.2,hz.1,hz.2]
    obtain ⟨z,hz,hval⟩ := ih (fun r => F (r+1)) y hs
    refine ⟨z,?_,?_⟩
    · simp only [Nat.cast_add,Nat.cast_one]
      constructor <;> linarith only [hy.1,hy.2,hz.1,hz.2]
    · exact he.symm.trans hval

/-- Actual derivative bounds transfer to the same finite difference bounds
on the exact sample interval. -/
theorem forwardDifference_mem_Icc (F : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) {lo hi : ℝ}
    (hd : ∀ r : ℕ, r < n → ∀ y ∈ Set.Icc x (x+n),
      HasDerivAt (F r) (F (r+1) y) y)
    (hb : ∀ y ∈ Set.Icc x (x+n), F n y ∈ Set.Icc lo hi) :
    forwardDifference n (F 0) x ∈ Set.Icc lo hi := by
  obtain ⟨y,hy,he⟩ := exists_forwardDifference_eq_derivative F n x hd
  rw [he]
  exact hb y hy

theorem forwardDifference_two (f : ℝ → ℝ) (x : ℝ) :
    forwardDifference 2 f x = f (x+2)-2*f (x+1)+f x := by
  change (f (x+1+1)-f (x+1))-(f (x+1)-f x) = _
  rw [show x+1+1 = x+2 by ring]
  ring

theorem forwardDifference_three (f : ℝ → ℝ) (x : ℝ) :
    forwardDifference 3 f x = f (x+3)-3*f (x+2)+3*f (x+1)-f x := by
  change forwardDifference 2 f (x+1)-forwardDifference 2 f x = _
  rw [forwardDifference_two,forwardDifference_two,
    show x+1+2 = x+3 by ring,show x+1+1 = x+2 by ring]
  ring

end WaveTurbulence.NumberTheory
