/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.MergeSmall
import Mathlib.Tactic

/-! # Star sums of the merged molecule

For `N = mergePair M v₁ v₂`: the darts of `N` are the darts of `M` that are not between `v₁` and `v₂`, with the atoms
`v₂ ↦ v₁`. Star sums of a function of the underlying dart:
* at an atom `v ≠ v₁` they are the star sums of `M`;
* at `v₁` they are the star sum at `v₁` plus the star sum at `v₂`, minus the sum over the pair darts, which vanishes when the
  summand is odd under `mate`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace MergeSum
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

/-- A sum over the darts of the merged molecule, written on the underlying darts. -/
theorem sum_off {E : Type*} [AddCommMonoid E] (P : D → Prop) [DecidablePred P] (F : D → E) :
    ∑ z ∈ (univ : Finset (OffPair M v₁ v₂)).filter (fun z => P z.val), F z.val =
      ∑ x : D, if M.ends x ≠ s(v₁, v₂) ∧ P x then F x else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij (fun z => z.val) ?_ ?_ ?_ ?_
  · intro z hz
    exact mem_filter.mpr ⟨mem_univ _, z.property, (mem_filter.mp hz).2⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro x hx
    obtain ⟨_, h1, h2⟩ := mem_filter.mp hx
    exact ⟨⟨x, h1⟩, mem_filter.mpr ⟨mem_univ _, h2⟩, rfl⟩
  · intro z _; rfl

/-- Star sums at an atom other than `v₁` are those of `M`. -/
theorem star_sum_far {E : Type*} [AddCommMonoid E] (F : D → E) {y : V} (h1 : y ≠ v₁) (h2 : y ≠ v₂) :
    ∑ z ∈ (mergePair M v₁ v₂ hv₁ hne).dartsAt y, F z.val = ∑ x ∈ M.dartsAt y, F x := by
  classical
  have key : ∀ z : OffPair M v₁ v₂, (mergePair M v₁ v₂ hv₁ hne).atom z = y ↔ M.atom z.val = y := by
    intro z
    rw [Merge.atom_eq]
    by_cases hz : M.atom z.val = v₂
    · rw [hz, mergeMap, if_pos rfl]; exact ⟨fun h => absurd h.symm h1, fun h => absurd h.symm h2⟩
    · rw [Merge.mergeMap_of_ne hz]
  have e1 : (mergePair M v₁ v₂ hv₁ hne).dartsAt y = (univ : Finset (OffPair M v₁ v₂)).filter
      (fun z => M.atom z.val = y) := by
    unfold Molecule.dartsAt
    ext z
    simp only [mem_filter, mem_univ, true_and]
    exact key z
  rw [e1, sum_off (M := M) (v₁ := v₁) (v₂ := v₂) (fun x => M.atom x = y) F]
  unfold Molecule.dartsAt
  rw [Finset.sum_filter]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : M.atom x = y
  · have : M.ends x ≠ s(v₁, v₂) := by
      intro h
      have hm : M.atom x ∈ M.ends x := Sym2.mem_mk_left _ _
      rw [h, hx] at hm
      rcases Sym2.mem_iff.mp hm with h' | h'
      · exact h1 h'
      · exact h2 h'
    simp [hx, this]
  · simp [hx]

/-- The darts between `v₁` and `v₂`. -/
def pairDarts (M : Molecule V D) (v₁ v₂ : V) : Finset D := univ.filter fun x => M.ends x = s(v₁, v₂)

/-- Star sum at the merged atom. -/
theorem star_sum_v₁ {E : Type*} [AddCommGroup E] (F : D → E) :
    ∑ z ∈ (mergePair M v₁ v₂ hv₁ hne).dartsAt v₁, F z.val + ∑ x ∈ pairDarts M v₁ v₂, F x =
      ∑ x ∈ M.dartsAt v₁, F x + ∑ x ∈ M.dartsAt v₂, F x := by
  classical
  have e1 : (mergePair M v₁ v₂ hv₁ hne).dartsAt v₁ = (univ : Finset (OffPair M v₁ v₂)).filter
      (fun z => M.atom z.val = v₁ ∨ M.atom z.val = v₂) := by
    unfold Molecule.dartsAt
    ext z
    simp only [mem_filter, mem_univ, true_and, Merge.atom_eq, Merge.mergeMap_eq_v₁]
  rw [e1, sum_off (M := M) (v₁ := v₁) (v₂ := v₂) (fun x => M.atom x = v₁ ∨ M.atom x = v₂) F]
  unfold Molecule.dartsAt pairDarts
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  by_cases hp : M.ends x = s(v₁, v₂)
  · have hat : M.atom x = v₁ ∨ M.atom x = v₂ := by
      have hm : M.atom x ∈ M.ends x := Sym2.mem_mk_left _ _
      rw [hp] at hm
      exact Sym2.mem_iff.mp hm
    rcases hat with h | h
    · simp [hp, h, hne]
    · simp [hp, h, hne.symm]
  · by_cases hat : M.atom x = v₁ ∨ M.atom x = v₂
    · rcases hat with h | h
      · simp [hp, h, hne]
      · simp [hp, h, hne.symm]
    · push Not at hat
      simp [hp, hat.1, hat.2]

/-- The sum over the pair darts of an odd function vanishes. -/
theorem sum_pair_odd {E : Type*} [AddCommGroup E] (F : D → E) (hodd : ∀ x, F (M.mate x) = - F x) :
    ∑ x ∈ pairDarts M v₁ v₂, F x = 0 := by
  classical
  refine Finset.sum_involution (fun x _ => M.mate x) ?_ ?_ ?_ ?_
  · intro x _; rw [hodd]; simp
  · intro x _ _ h
    exact M.mate_ne x h
  · intro x hx
    unfold pairDarts at hx ⊢
    rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [ends_mate M, hx.2, Sym2.eq_swap]
  · intro x _; exact M.mate_mate x

end MergeSum
end WaveTurbulence.FinalCountG8
