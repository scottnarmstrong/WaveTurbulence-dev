/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ReciprocalCounting
public import Mathlib.Data.Nat.ModEq

/-!
# Reciprocal counting in a residue class

The quotient index parametrizes a residue block. This transfers the affine
harmonic estimate to arbitrary subsets of a residue class, without assuming
that such subsets are intervals.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- A nonnegative sum on a subset of one residue class is bounded by the full
progression with quotient indices up to `N/q`. -/
theorem sum_residue_le (S : Finset ℕ) (N q r : ℕ)
    (hS : ∀ j ∈ S, j < N) (hr : ∀ j ∈ S, j % q = r)
    (F : ℕ → ℝ) (hF : ∀ j, 0 ≤ F j) :
    (∑ j ∈ S, F j) ≤ ∑ k ∈ range (N / q + 1), F (q * k + r) := by
  refine sum_le_sum_of_injOn (fun j => j / q) ?_ ?_ ?_ ?_
  · intro i hi j hj heq
    dsimp at heq
    have hiq := Nat.mod_add_div i q
    have hjq := Nat.mod_add_div j q
    rw [hr i hi, heq] at hiq
    rw [hr j hj] at hjq
    omega
  · intro k hk
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
    simp only [mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (hS j hj).le)
  · intro j hj
    have heq : q * (j / q) + r = j := by
      rw [add_comm, ← hr j hj]
      exact Nat.mod_add_div j q
    rw [heq]
  · intro k _ _
    exact hF _

/-- A residue class has at most one index for each quotient. -/
theorem card_residue_le (S : Finset ℕ) (N q r : ℕ)
    (hS : ∀ j ∈ S, j < N) (hr : ∀ j ∈ S, j % q = r) :
    (S.card : ℝ) ≤ ((N / q + 1 : ℕ) : ℝ) := by
  have h := sum_residue_le S N q r hS hr (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
  simpa only [sum_const, card_range, nsmul_eq_mul, mul_one] using h


/-- A cap bound in one residue class, with no nonzero-step assumption. -/
theorem sum_cappedInv_residue_le_trivial (S : Finset ℕ) (N q r : ℕ)
    (hS : ∀ j ∈ S, j < N) (hr : ∀ j ∈ S, j % q = r)
    (T x δ : ℝ) (hT : 0 ≤ T) :
    (∑ j ∈ S, cappedInv T (x + δ * j)) ≤ ((N / q + 1 : ℕ) : ℝ) * T := by
  refine (sum_residue_le S N q r hS hr (fun j => cappedInv T (x + δ * j))
    (fun j => cappedInv_nonneg hT _)).trans ?_
  calc
    _ ≤ ∑ k ∈ range (N / q + 1), T := sum_le_sum (fun k _ => cappedInv_le T _)
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

/-- The refined affine bound in a residue class. The step in the quotient
index is `δq`, giving the essential gain `1/(q|δ|)`. -/
theorem sum_cappedInv_residue_le (S : Finset ℕ) (N q r : ℕ)
    (hq : 0 < q) (hS : ∀ j ∈ S, j < N) (hr : ∀ j ∈ S, j % q = r)
    (T x δ : ℝ) (hT : 0 ≤ T) (hδ : δ ≠ 0) :
    (∑ j ∈ S, cappedInv T (x + δ * j)) ≤
      T + 4 / (|δ| * q) * (harmonic (N / q + 1) : ℝ) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hq)
  refine (sum_residue_le S N q r hS hr (fun j => cappedInv T (x + δ * j))
    (fun j => cappedInv_nonneg hT _)).trans ?_
  have heq (k : ℕ) : x + δ * (q * k + r : ℕ) =
      (x + δ * r) + (δ * q) * k := by push_cast; ring
  simp_rw [heq]
  have h := sum_cappedInv_affine_le T (x + δ * r) (δ * q) (N / q + 1) hT
    (mul_ne_zero hδ hq')
  simpa only [abs_mul, abs_of_pos (show (0 : ℝ) < q from Nat.cast_pos.mpr hq)] using h

end WaveTurbulence.WeylSums
