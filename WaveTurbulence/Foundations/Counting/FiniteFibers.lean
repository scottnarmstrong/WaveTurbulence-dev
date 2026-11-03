/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Real-valued finite-fiber density estimates

A direct specialization of Mathlib's weighted pigeonhole principle for the
coordinate-fixing step in DH23 `basiccount0pre` (2).
-/

public section

namespace WaveTurbulence.Counting

/-- Fixing a finite projection with at most `N` values preserves density at
least `A` in one fiber whenever the original family has at least `A*N` points. -/
theorem exists_large_real_fiber {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (hs : s.Nonempty) {A N : ℝ}
    (hA : 0 ≤ A) (hproj : ((s.image f).card:ℝ) ≤ N) (hdense : A*N ≤ (s.card:ℝ)) :
    ∃ z ∈ s.image f, A ≤ ((s.filter (fun x => f x = z)).card:ℝ) := by
  have hm := mul_le_mul_of_nonneg_right hproj hA
  have htotal : (s.image f).card • A ≤ ∑ _x ∈ s, (1:ℝ) := by
    simp only [nsmul_eq_mul,Finset.sum_const,mul_one]
    nlinarith only [hm,hdense]
  obtain ⟨z,hz,hb⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (f := f) (w := fun _ : α => (1:ℝ)) (t := s.image f)
    (fun x hx => Finset.mem_image_of_mem f hx) (hs.image f) htotal
  refine ⟨z,hz,?_⟩
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hb

/-- Summing a uniform bound over the actual image of a finite projection. -/
theorem card_le_image_card_mul_of_fiber_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) {C : ℝ}
    (h : ∀ z ∈ s.image f, ((s.filter (fun x => f x = z)).card:ℝ) ≤ C) :
    (s.card:ℝ) ≤ ((s.image f).card:ℝ)*C := by
  rw [Finset.card_eq_sum_card_image f s,Nat.cast_sum]
  calc
    _ ≤ ∑ _z ∈ s.image f, C := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

end WaveTurbulence.Counting
