/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostMain2
/-! G2-GHOST part 9: **the charged ghost-aware triangle deviation** (R38 item 1; DH23 Prop 9.4, Step 2, L1777,
L1793--L1796, with the ghost refund of the research notes NOTES 3a--3d). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem card_ghost_split (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j) :
    (Finset.univ.filter gh).card =
      (Finset.univ.filter ag).card + (Finset.univ.filter fun j => gh j ∧ ¬ ag j).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h; by_cases h' : ag j
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h)
      · exact hag j h
      · exact h.1
  · rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2.2 h1

theorem excess_mono_const {K K' X : ℝ} (hK : K ≤ K') (hX : 0 ≤ X) : K * X ≤ K' * X :=
  mul_le_mul_of_nonneg_right hK hX

end WaveTurbulence.FinalCount
