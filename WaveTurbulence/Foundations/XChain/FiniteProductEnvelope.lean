/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-! A finite collection of independent label assignments is bounded by coordinate sum envelopes. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_prod_le_prod_finite_sum_bounds {ι : Type*} [Fintype ι] {α : ι → Type*}
    (f : (i : ι) → α i → ℝ) (hf : ∀ i a, 0 ≤ f i a) (M : ι → ℝ)
    (hM : ∀ i (u : Finset (α i)), ∑ a ∈ u, f i a ≤ M i)
    (u : Finset ((i : ι) → α i)) : (∑ a ∈ u, ∏ i, f i (a i)) ≤ ∏ i, M i := by
  classical
  calc
    _ ≤ ∑ a ∈ Fintype.piFinset (fun i => u.image (fun a => a i)), ∏ i, f i (a i) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact Fintype.mem_piFinset.mpr (fun i => mem_image_of_mem (fun a => a i) ha)
      · intro _ _ _
        exact prod_nonneg (fun i _ => hf i _)
    _ = ∏ i, ∑ a ∈ u.image (fun a => a i), f i a := (prod_univ_sum _ _).symm
    _ ≤ ∏ i, M i := prod_le_prod₀
      (fun i _ => sum_nonneg (fun a _ => hf i a)) (fun i _ => hM i _)

end WaveTurbulence.Induct
