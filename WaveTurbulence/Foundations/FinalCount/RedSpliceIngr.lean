/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceRev
public import WaveTurbulence.Foundations.FinalCount.S1Collection
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the ingredients of a VC group

A block cannot also be a hyper-block (`vc_not_hyper`: the joint internal degrees are `2` against `3`), so every
ingredient of a VC group, in the sense of `IsIngredient`, is a member of the unique spine in one of the two joint
orders (`isIngredient_vc`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole WaveTurbulence.Stage1

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- A block is not a hyper-block. -/
theorem vc_not_hyper {S : Finset V} {a b j1 j2 : V} (hB : M.IsBlock S a b) (hH : M.IsHyperBlock S j1 j2) :
    False := by
  obtain ⟨h1, h2, h3⟩ := hyperBlock_degrees M hH
  obtain ⟨da, db⟩ := block_joint_degrees M hB
  have hj1 : j1 ∈ S := by
    obtain ⟨e, _, hb⟩ := hH
    exact hb.2.1
  have hj2 : j2 ∈ S := by
    obtain ⟨e, _, hb⟩ := hH
    exact hb.2.2.1
  by_cases ha : j1 = a
  · subst ha; omega
  by_cases hb' : j1 = b
  · subst hb'; omega
  have := hB.2.2.2.2.2.2.2.2.1 j1 hj1 ha hb'
  have := h3 j1 hj1
  omega

/-- Every ingredient (in the sense of `IsIngredient`) of a VC group is a member of its spine. -/
theorem isIngredient_vc (hM : M.IsMolecule) {S T : Finset V} {a b : V} {L : List (Finset V × V × V)}
    (hB : M.IsBlock S a b) (hs : Spine M L S a b) (h : IsIngredient M S T) :
    ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L := by
  rcases h with ⟨a', b', n, x, y, hB', hI⟩ | ⟨a', b', e, n, x, y, hends, _, hBe, _⟩
  · have hj := Vine.block_joints_unique M hB hB'
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      obtain ⟨L', hL', hm⟩ := Spine.mem_of_ingredient hI
      rw [Spine.unique hM hL' hs hB] at hm
      exact ⟨x, y, Or.inl hm⟩
    · subst h1; subst h2
      rcases hs.ingredient_mem_or_reverse hM hB hI with hm | hm
      · exact ⟨y, x, Or.inl hm⟩
      · exact ⟨x, y, Or.inl hm⟩
  · exact (vc_not_hyper hB ⟨e, hends, hBe⟩).elim

end WaveTurbulence.RedSplice
