/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
import Mathlib.Tactic

/-! # The finite label set of the five-atom side core and its inserted rungs -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- Five old side-core labels and the contiguous two-rail allocation. -/
@[expose] def sideLabels (N k : ℕ) : Finset ℕ :=
  {4,5,6,7,8} ∪ (range (2*k)).image (N+·)

/-- Membership retains exactly the five old labels and the fresh interval. -/
theorem mem_sideLabels_iff (N k i : ℕ) : i ∈ sideLabels N k ↔
    i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ (N ≤ i ∧ i<N+2*k) := by
  have hrange : i ∈ (range (2*k)).image (N+·) ↔ N ≤ i ∧ i<N+2*k := by
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      have := mem_range.mp hj
      constructor <;> omega
    · rintro ⟨hlo,hhi⟩
      exact mem_image.mpr ⟨i-N,mem_range.mpr (by omega),by omega⟩
  simp only [sideLabels,mem_union,mem_insert,mem_singleton,hrange,or_assoc]

/-- With fresh labels beyond the old core, the side has exactly 5+2k atoms. -/
theorem sideLabels_card (N k : ℕ) (hN : 9 ≤ N) : (sideLabels N k).card=5+2*k := by
  have hd : Disjoint ({4,5,6,7,8} : Finset ℕ) ((range (2*k)).image (N+·)) := by
    apply disjoint_left.mpr
    intro i hi hj
    have hi9 : i<9 := by
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> omega
    obtain ⟨j,_hj,he⟩ := mem_image.mp hj
    omega
  rw [sideLabels,card_union_of_disjoint hd,
    card_image_of_injective _ (fun _ _ he => Nat.add_left_cancel he),card_range]
  have hc : ({4,5,6,7,8} : Finset ℕ).card=5 := by decide
  rw [hc]

end WaveTurbulence.Vine
