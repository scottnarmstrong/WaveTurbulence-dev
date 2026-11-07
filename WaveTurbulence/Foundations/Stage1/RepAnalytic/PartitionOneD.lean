/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # A one-dimensional smooth partition of unity on `ℝ` by integer translates

`θ(y) = s(y) - s(y - 1)` with `s` the smooth step `Real.smoothTransition`.  Then `θ ≥ 0` is smooth,
supported in `[0, 2]`, and `∑_{n ∈ ℤ} θ(x - n + 1) = 1` (the sum telescopes).  This is the one-dimensional
ingredient of the unit-ball partition of unity of `RepAnalytic.Partition` (TARGET L1959: "restricting
each `k_ℓ` to a unit ball `|k_ℓ - k_ℓ⁰| ≤ 1`").
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open Finset
open scoped ContDiff

/-- The bump `θ(y) = s(y) - s(y-1)`, `s = Real.smoothTransition`. -/
noncomputable def theta1 (y : ℝ) : ℝ := Real.smoothTransition y - Real.smoothTransition (y - 1)

theorem theta1_nonneg (y : ℝ) : 0 ≤ theta1 y := by
  unfold theta1
  have := Real.smoothTransition.monotone (show y - 1 ≤ y by linarith)
  linarith

theorem theta1_le_one (y : ℝ) : theta1 y ≤ 1 := by
  unfold theta1
  linarith [Real.smoothTransition.le_one y, Real.smoothTransition.nonneg (y - 1)]

theorem theta1_eq_zero {y : ℝ} (h : y ≤ 0 ∨ 2 ≤ y) : theta1 y = 0 := by
  unfold theta1
  rcases h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos h, Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le (by linarith)]
    simp

theorem theta1_pos_lt {y : ℝ} (h : theta1 y ≠ 0) : 0 < y ∧ y < 2 := by
  by_contra hc
  apply h
  apply theta1_eq_zero
  by_cases h0 : y ≤ 0
  · exact Or.inl h0
  · right
    by_contra h2
    exact hc ⟨by linarith, by linarith⟩

theorem theta1_contDiff : ContDiff ℝ ∞ theta1 :=
  Real.smoothTransition.contDiff.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

private theorem telescope_image (g : ℤ → ℝ) (a : ℤ) (k : ℕ) :
    ∑ n ∈ (Finset.range k).image (fun j : ℕ => a + (j : ℤ)), (g n - g (n + 1)) = g a - g (a + k) := by
  rw [Finset.sum_image (fun x _ y _ h => by exact_mod_cast (add_left_cancel h))]
  have := Finset.sum_range_sub' (fun j : ℕ => g (a + (j : ℤ))) k
  simpa [add_assoc] using this

/-- The translates `θ(x - n + 1)`, `n ∈ ℤ`, sum to `1` (finitely many are nonzero). -/
theorem hasSum_theta1 (x : ℝ) : HasSum (fun n : ℤ => theta1 (x - n + 1)) 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (|x| + 1)
  have hx1 := neg_abs_le x
  have hx2 := le_abs_self x
  set S : Finset ℤ := (Finset.range (2 * N + 1)).image (fun j : ℕ => -(N : ℤ) + (j : ℤ)) with hS
  have hmem : ∀ n : ℤ, n ∈ S ↔ -(N : ℤ) ≤ n ∧ n ≤ N := by
    intro n
    simp only [hS, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · intro h
      exact ⟨(n + N).toNat, by omega, by omega⟩
  have hzero : ∀ n ∉ S, theta1 (x - n + 1) = 0 := by
    intro n hn
    rw [hmem] at hn
    apply theta1_eq_zero
    by_cases h : -(N : ℤ) ≤ n
    · have h2 : (N : ℤ) < n := by omega
      have h3 : (N : ℝ) + 1 ≤ n := by exact_mod_cast h2
      left; linarith
    · have h2 : n < -(N : ℤ) := by omega
      have h3 : (n : ℝ) + 1 ≤ -(N : ℝ) := by exact_mod_cast (show n + 1 ≤ -(N : ℤ) by omega)
      right; linarith
  have h : HasSum (fun n : ℤ => theta1 (x - n + 1)) (∑ n ∈ S, theta1 (x - n + 1)) :=
    hasSum_sum_of_ne_finset_zero hzero
  convert h using 1
  set g : ℤ → ℝ := fun n => Real.smoothTransition (x - n + 1) with hg
  have hterm : ∀ n : ℤ, theta1 (x - n + 1) = g n - g (n + 1) := by
    intro n
    simp only [theta1, hg]
    push_cast
    ring_nf
  simp_rw [hterm]
  rw [hS, telescope_image g (-(N : ℤ)) (2 * N + 1)]
  simp only [hg]
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.zero_of_nonpos]
  · simp
  · push_cast; linarith
  · push_cast; linarith

end WaveTurbulence.RepAnalytic
