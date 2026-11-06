/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Data.Set.Function
/-! Choosing one admissible bin gives a disjoint refinement of any cover. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set

/-- A cover can be refined without increasing its index type or any individual piece. -/
theorem exists_unique_cover_refinement {X J : Type*} (t : Set X) (c : J → Set X)
    (hcover : ∀ x ∈ t, ∃ j, x ∈ c j) :
    ∃ s : J → Set X, (∀ j, s j ⊆ c j) ∧ (∀ x ∈ t, ∃! j, x ∈ s j) := by
  classical
  let pick (x : X) : Option J := if h : x ∈ t then some (Classical.choose (hcover x h)) else none
  refine ⟨fun j => {x | pick x = some j}, ?_, ?_⟩
  · intro j x hx
    change pick x = some j at hx
    by_cases ht : x ∈ t
    · have he : Classical.choose (hcover x ht) = j := by
        simpa only [pick, dite_eq_left ht, Option.some.injEq] using hx
      exact he ▸ Classical.choose_spec (hcover x ht)
    · simp [pick, ht] at hx
  · intro x ht
    refine ⟨Classical.choose (hcover x ht), ?_, ?_⟩
    · change pick x = some _
      simp only [pick, dite_eq_left ht]
    · intro j hj
      change pick x = some j at hj
      exact (Option.some.inj ((by simp only [pick, dite_eq_left ht] : pick x =
        some (Classical.choose (hcover x ht))).symm.trans hj)).symm

end WaveTurbulence.LGSpine
