/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.SubObjU2
public import WaveTurbulence.Foundations.TVine.Struct.MBridge
import Mathlib.Tactic

/-!
# From L6's vine-like objects (`Src.Object`) to L1's sub-objects (`SubObj`) (packet L3)

* `groupGraph_induce`: `induce (groupGraph M S) T = groupGraph M T` for `T ⊆ S`;
* `groupGraph_eraseBond`: the group graph of `M` with the bond `e` removed is `eraseBond (groupGraph M T) (ends e)`;
* `suOf U`: the sub-object `(S(U), upper, lower, hyper?)` of an `Src.Object`;
* `vineLike_suOf`: for `γ ≤ 1/2` and `S(U) ⊊ S` (a block), `suOf U` is a vine-like sub-object of `groupGraph M S`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u v

section graphs

variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem count_groupBonds_sub (M : Molecule V D) {S T : Finset V} (hT : T ⊆ S) {e : Sym2 V}
    (he : e ∈ T.sym2) : (M.groupBonds S).count e = (M.groupBonds T).count e := by
  rw [← groupGraph_mult, ← groupGraph_mult, groupGraph_mult_eq_card, groupGraph_mult_eq_card]
  congr 1
  ext x
  simp only [Finset.mem_filter, mem_groupDarts]
  constructor
  · rintro ⟨⟨ho, -, -⟩, hx⟩
    have := Finset.mem_sym2_iff.mp he
    exact ⟨⟨ho, this _ (by rw [← hx]; exact Sym2.mem_mk_left _ _),
      this _ (by rw [← hx]; exact Sym2.mem_mk_right _ _)⟩, hx⟩
  · rintro ⟨⟨ho, h1, h2⟩, hx⟩; exact ⟨⟨ho, hT h1, hT h2⟩, hx⟩

/-- **The induced subgraph of a group graph is the group graph of the subset.** -/
theorem groupGraph_induce (M : Molecule V D) {S T : Finset V} (hT : T ⊆ S) :
    induce (groupGraph M S) T = groupGraph M T := by
  refine Core.ext rfl fun e => ?_
  show (if e ∈ T.sym2 then (M.groupBonds S).count e else 0) = (M.groupBonds T).count e
  split_ifs with he
  · exact count_groupBonds_sub M hT he
  · symm
    rw [Multiset.count_eq_zero]
    intro hm
    exact he ((groupGraph M T).supp e (by rw [groupGraph_mult]; exact Multiset.count_ne_zero.mpr hm) |>
      fun h => Finset.mem_sym2_iff.mpr h)

/-- **The group graph after erasing a bond of the group** (one copy of its ends removed). -/
theorem groupGraph_eraseBond (M : Molecule V D) {T : Finset V} {e : D} (he : M.InGroup T e) :
    groupGraph (M.eraseBond e) T = Core.eraseBond (groupGraph M T) (M.ends e) := by
  classical
  refine Core.ext rfl fun f => ?_
  rw [groupGraph_mult_eq_card]
  show _ = if f = M.ends e then (groupGraph M T).mult f - 1 else (groupGraph M T).mult f
  rw [groupGraph_mult_eq_card]
  -- the darts of the erased molecule are those of `M` other than `e`, `mate e`
  set A := (groupDarts M T).filter fun x => M.ends x = f with hA
  have hcard : ((groupDarts (M.eraseBond e) T).filter fun x => (M.eraseBond e).ends x = f).card =
      (A.filter fun x => x ≠ e ∧ x ≠ M.mate e).card := by
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, mem_groupDarts] at hx
      simp only [hA, Finset.mem_filter, mem_groupDarts]
      exact ⟨⟨⟨hx.1.1, hx.1.2⟩, hx.2⟩, x.2⟩
    · intro x _ y _ h; exact Subtype.ext h
    · intro y hy
      simp only [hA, Finset.mem_filter, mem_groupDarts] at hy
      refine ⟨⟨y, hy.2⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, mem_groupDarts]
      exact ⟨⟨hy.1.1.1, hy.1.1.2⟩, hy.1.2⟩
  rw [hcard]
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun x => x ≠ e ∧ x ≠ M.mate e)
  have hends : M.ends (M.mate e) = M.ends e := by
    simp only [Molecule.ends, M.mate_mate]; exact Sym2.eq_swap
  split_ifs with hf
  · -- exactly one of `e`, `mate e` is an outgoing dart, and both have ends `f`
    have hneg : (A.filter fun x => ¬ (x ≠ e ∧ x ≠ M.mate e)).card = 1 := by
      rw [Finset.card_eq_one]
      by_cases ho : M.out e = true
      · refine ⟨e, ?_⟩
        ext x
        simp only [hA, Finset.mem_filter, mem_groupDarts, not_and_or, not_not, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨⟨hxo, -⟩, -⟩, h | h⟩
          · exact h
          · exfalso; rw [h, M.out_mate, ho] at hxo; simp at hxo
        · rintro rfl; exact ⟨⟨⟨ho, he⟩, hf.symm⟩, Or.inl rfl⟩
      · refine ⟨M.mate e, ?_⟩
        ext x
        simp only [hA, Finset.mem_filter, mem_groupDarts, not_and_or, not_not, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨⟨hxo, -⟩, -⟩, h | h⟩
          · exfalso; rw [h] at hxo; exact ho hxo
          · exact h
        · rintro rfl
          refine ⟨⟨⟨by rw [M.out_mate]; simpa using ho, he.2, by rw [M.mate_mate]; exact he.1⟩, ?_⟩, Or.inr rfl⟩
          rw [hends, hf]
    omega
  · have hneg : (A.filter fun x => ¬ (x ≠ e ∧ x ≠ M.mate e)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      simp only [hA, Finset.mem_filter] at hx
      simp only [not_and_or, not_not]
      rintro (rfl | rfl)
      · exact hf hx.2.symm
      · exact hf (by rw [← hends]; exact hx.2.symm)
    omega

end graphs

end WaveTurbulence.TVine.Struct
