/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.FiniteFibers
import Mathlib.Tactic

/-! # A finite sparse/dense fiber split -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- Split the actual image by its fiber cardinality. This finite identity
is applied to the concrete dot-product fibers, with no density witness assumed. -/
theorem card_le_sparse_add_dense {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (f : ι → κ) {A B : ℝ} (hB : 0 ≤ B)
    (hcap : ∀ x ∈ s.image f, (((s.filter (fun q => f q = x)).card) : ℝ) ≤ A) :
    (s.card : ℝ) ≤ ((s.image f).card : ℝ)*B+
      (((s.image f).filter (fun x => B < (((s.filter (fun q => f q = x)).card) : ℝ))).card : ℝ)*A := by
  classical
  let X := s.image f
  let fiber := fun x => (((s.filter (fun q => f q = x)).card) : ℝ)
  let high := fun x => B < fiber x
  have he : (s.card : ℝ) = ∑ x ∈ X, fiber x := by
    rw [card_eq_sum_card_image f s,Nat.cast_sum]
  rw [he,← sum_filter_add_sum_filter_not X high fiber]
  have hlow : (∑ x ∈ X.filter (fun x => ¬high x), fiber x) ≤ (X.card : ℝ)*B := by
    calc
      _ ≤ ∑ _x ∈ X.filter (fun x => ¬high x), B := sum_le_sum (by
        intro x hx
        exact le_of_not_gt (mem_filter.mp hx).2)
      _ = ((X.filter (fun x => ¬high x)).card : ℝ)*B := by rw [sum_const,nsmul_eq_mul]
      _ ≤ (X.card : ℝ)*B := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_filter_le _ _)) hB
  have hhigh : (∑ x ∈ X.filter high, fiber x) ≤ ((X.filter high).card : ℝ)*A := by
    calc
      _ ≤ ∑ _x ∈ X.filter high, A := sum_le_sum (by
        intro x hx
        exact hcap x (mem_filter.mp hx).1)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have hh := add_le_add hhigh hlow
  simpa only [X,high,fiber,add_comm] using hh

end WaveTurbulence.CountLemmas
