/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineSubsetVCRemoval
public import WaveTurbulence.Foundations.Spine.SourceDiamondClosed
import Mathlib.Tactic

/-!
# S4-SHAPE: structure of a two-double-bond chain `a = x = b`

The universe's `subsetvc_simultaneous_removal_connected` removes only pieces that are single vines (`IsSomeVine`). A chain of two
double bonds (`DoubleChain M S a b 2`, three atoms) is not a vine (`isVine_typeI_of_card_lt_four`), so it is not covered, although
TARGET Lemma `subsetvc` and the three-atom case of Step 1 need it. This file proves the local structure used to reduce such a piece
to its first double bond.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.Vine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem doubleChain_two_split {M : Molecule V D} {S : Finset V} {a b : V} (h : DoubleChain M S a b 2) :
    ∃ x, S = {a, x, b} ∧ M.IsVine .I {a, x} a x ∧ M.IsVine .I {x, b} x b ∧ a ≠ b := by
  cases h with
  | @append S' T' a' b' c' n h1 h2 h3 h4 =>
    cases h1 with
    | single h1 =>
      have e1 := typeI_atoms h1
      have e2 := typeI_atoms h2
      refine ⟨b', ?_, ?_, ?_, h4⟩
      · rw [e1, e2]; ext v; simp
      · rw [← e1]; exact h1
      · rw [← e2]; exact h2
    | append h _ _ _ => cases h

/-- The darts at the middle atom `x` of `a = x = b`: each lies in the group of `{a,x}` and joins `x` to `a`, or lies in the group of
`{x,b}` and joins `x` to `b`. -/
theorem dart_at_mid {M : Molecule V D} (hM : M.IsMolecule) {a x b : V} (hab : a ≠ b)
    (h1 : M.IsVine .I {a, x} a x) (h2 : M.IsVine .I {x, b} x b) {z : D} (hz : M.atom z = x) :
    (M.InGroup {a, x} z ∧ M.atom (M.mate z) = a) ∨ (M.InGroup {x, b} z ∧ M.atom (M.mate z) = b) := by
  have hB1 : M.IsBlock {a, x} x a := Mole.block_swap_joints M h1.1
  have hB2 := h2.1
  have hxa : x ≠ a := fun h => h1.1.2.2.2.1 h.symm
  have hxb : x ≠ b := fun h => hB2.2.2.2.1 h
  have hxat : x ∈ M.atoms := hB2.1 hB2.2.1
  have d1 := (Mole.block_joint_degrees M hB1).1
  have d2 := (Mole.block_joint_degrees M hB2).1
  set T1 := (M.dartsAt x).filter fun y => M.InGroup {a, x} y with hT1
  set T2 := (M.dartsAt x).filter fun y => M.InGroup {x, b} y with hT2
  have noloop1 : ∀ y, M.atom y = x → M.InGroup {a, x} y → M.atom (M.mate y) = a := by
    intro y hy hg
    have hm := hg.2
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with hm | hm
    · exact hm
    · exact (LGSpine.block_joint_no_loop hB1 hy hm hg).elim
  have noloop2 : ∀ y, M.atom y = x → M.InGroup {x, b} y → M.atom (M.mate y) = b := by
    intro y hy hg
    have hm := hg.2
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with hm | hm
    · exact (LGSpine.block_joint_no_loop hB2 hy hm hg).elim
    · exact hm
  have hdisj : Disjoint T1 T2 := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    have hy := (Mole.mem_dartsAt M x y).mp (mem_filter.mp hy1).1
    have e1 := noloop1 y hy (mem_filter.mp hy1).2
    have e2 := noloop2 y hy (mem_filter.mp hy2).2
    exact hab (e1.symm.trans e2)
  have hcard : (T1 ∪ T2).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj]
    have c1 : T1.card = 2 := d1
    have c2 : T2.card = 2 := d2
    omega
  have hsub : T1 ∪ T2 ⊆ M.dartsAt x := fun y hy => by
    rcases mem_union.mp hy with h | h <;> exact (mem_filter.mp h).1
  have hle : (M.dartsAt x).card ≤ 4 := by
    have := Mole.deg_le_four M hM hxat
    exact this
  have heq : T1 ∪ T2 = M.dartsAt x := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hzm : z ∈ M.dartsAt x := (Mole.mem_dartsAt M x z).mpr hz
  rw [← heq] at hzm
  rcases mem_union.mp hzm with h | h
  · exact Or.inl ⟨(mem_filter.mp h).2, noloop1 z hz (mem_filter.mp h).2⟩
  · exact Or.inr ⟨(mem_filter.mp h).2, noloop2 z hz (mem_filter.mp h).2⟩

/-- At a joint `j` of a block `P`, a two-atom sub-block `{j, m} ⊆ P` already uses both internal darts of `P` there: every dart of
`P`'s group at `j` lies in the group of `{j, m}` and ends at `m`. -/
theorem joint_darts_pair {M : Molecule V D} {P : Finset V} {j k m : V} (hP : M.IsBlock P j k)
    (hA : M.IsBlock {j, m} j m) (hAP : ({j, m} : Finset V) ⊆ P) {z : D} (hz : M.atom z = j)
    (hg : M.InGroup P z) : M.InGroup {j, m} z ∧ M.atom (M.mate z) = m := by
  have dP := (Mole.block_joint_degrees M hP).1
  have dA := (Mole.block_joint_degrees M hA).1
  have hsub : ((M.dartsAt j).filter fun y => M.InGroup {j, m} y) ⊆ (M.dartsAt j).filter fun y => M.InGroup P y := by
    intro y hy
    obtain ⟨h1, h2⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨h1, hAP h2.1, hAP h2.2⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    have c1 : ((M.dartsAt j).filter fun y => M.InGroup P y).card = 2 := dP
    have c2 : ((M.dartsAt j).filter fun y => M.InGroup {j, m} y).card = 2 := dA
    omega)
  have hzP : z ∈ (M.dartsAt j).filter fun y => M.InGroup P y :=
    mem_filter.mpr ⟨(Mole.mem_dartsAt M j z).mpr hz, hg⟩
  rw [← heq] at hzP
  have hzA := (mem_filter.mp hzP).2
  refine ⟨hzA, ?_⟩
  have hm := hzA.2
  simp only [mem_insert, mem_singleton] at hm
  rcases hm with hm | hm
  · exact (LGSpine.block_joint_no_loop hA hz hm hzA).elim
  · exact hm

end WaveTurbulence.Subpro
