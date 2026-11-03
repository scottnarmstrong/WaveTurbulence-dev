/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Partial summation with a decreasing nonnegative weight

This helper transfers a bound for actual partial sums to a weighted sum.
It is not an exponent-pair theorem: the partial-sum bound is an explicit
input to the elementary transfer.
-/

public section

namespace WaveTurbulence.VdCB

/-- A decreasing nonnegative weight costs only its initial value when
all actual initial partial sums have a common bound. -/
theorem norm_sum_range_antitone_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ℕ → ℝ) (z : ℕ → E) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w)
    (N : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ m ≤ N, ‖∑ i ∈ Finset.range m, z i‖ ≤ B) :
    ‖∑ i ∈ Finset.range N, w i • z i‖ ≤ w 0 * B := by
  cases N with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, norm_zero] using mul_nonneg (hw0 0) hB
  | succ n =>
    rw [Finset.sum_range_by_parts w z (n + 1)]
    simp only [Nat.add_sub_cancel]
    have hfirst : ‖w n • ∑ i ∈ Finset.range (n + 1), z i‖ ≤ w n * B := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 n)]
      exact mul_le_mul_of_nonneg_left (hpartial (n + 1) le_rfl) (hw0 n)
    have hterm (i : ℕ) (hi : i ∈ Finset.range n) :
        ‖(w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), z j‖ ≤ (w i - w (i + 1)) * B := by
      have hmono : w (i + 1) ≤ w i := hw (Nat.le_succ i)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
      exact mul_le_mul_of_nonneg_left (hpartial (i + 1) (by have := Finset.mem_range.mp hi; omega))
        (sub_nonneg.mpr hmono)
    have hsum : (∑ i ∈ Finset.range n, (w i - w (i + 1))) = w 0 - w n := by
      have hh := Finset.sum_range_sub w n
      rw [show (fun i => w i - w (i + 1)) = (fun i => -(w (i + 1) - w i)) by funext i; ring]
      rw [Finset.sum_neg_distrib, hh]
      ring
    calc
      _ ≤ ‖w n • ∑ i ∈ Finset.range (n + 1), z i‖ +
          ‖∑ i ∈ Finset.range n, (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), z j‖ := norm_sub_le _ _
      _ ≤ w n * B + ∑ i ∈ Finset.range n, (w i - w (i + 1)) * B :=
        add_le_add hfirst ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
      _ = w 0 * B := by rw [← Finset.sum_mul, hsum]; ring

end WaveTurbulence.VdCB
