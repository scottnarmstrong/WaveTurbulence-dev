/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.EnumerationSum
/-! Sum over a finite cover of actual objects, allowing overlapping code presentations. -/
public section
namespace WaveTurbulence.LGSpine
open Finset

theorem norm_sum_le_cover {ι κ : Type*} [DecidableEq ι] (s : Finset ι) (t : Finset κ)
    (S : κ → Finset ι) (f : ι → ℂ)
    (hcover : ∀ i ∈ s, ∃ j ∈ t, i ∈ S j) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ j ∈ t, ∑ i ∈ S j, ‖f i‖ := by
  classical
  calc
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, if i ∈ S j then ‖f i‖ else 0 := by
      apply sum_le_sum
      intro i hi
      obtain ⟨j, hj, hij⟩ := hcover i hi
      have h := single_le_sum (s := t)
        (f := fun j => if i ∈ S j then ‖f i‖ else 0)
        (fun j _ => by split_ifs <;> positivity) hj
      simpa only [if_pos hij] using h
    _ = ∑ j ∈ t, ∑ i ∈ s.filter (fun i => i ∈ S j), ‖f i‖ := by
      rw [sum_comm]
      simp only [sum_filter]
    _ ≤ ∑ j ∈ t, ∑ i ∈ S j, ‖f i‖ := by
      apply sum_le_sum
      intro j _
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact (mem_filter.mp hi).2
      · intro i _ _
        exact norm_nonneg _

theorem norm_sum_le_cover_count {ι κ : Type*} [DecidableEq ι] (s : Finset ι) (t : Finset κ)
    (S : κ → Finset ι) (f : ι → ℂ) (M N : κ → ℝ)
    (hcover : ∀ i ∈ s, ∃ j ∈ t, i ∈ S j)
    (hM : ∀ j ∈ t, 0 ≤ M j)
    (hcount : ∀ j ∈ t, ((S j).card : ℝ) ≤ N j)
    (hbound : ∀ j ∈ t, ∀ i ∈ S j, ‖f i‖ ≤ M j) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ j ∈ t, N j * M j := by
  apply (norm_sum_le_cover s t S f hcover).trans
  apply sum_le_sum
  intro j hj
  calc
    ∑ i ∈ S j, ‖f i‖ ≤ ∑ _i ∈ S j, M j := sum_le_sum (hbound j hj)
    _ = ((S j).card : ℝ) * M j := by simp
    _ ≤ N j * M j := mul_le_mul_of_nonneg_right (hcount j hj) (hM j hj)

end WaveTurbulence.LGSpine
