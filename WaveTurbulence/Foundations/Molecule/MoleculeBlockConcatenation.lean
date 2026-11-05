/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockSameJoints
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-!
# Incidence calculus for concatenating connected blocks

TARGET `defblock`, DH23 Definition 4.10 and Lemma 4.11(b). An edge from
outside a block can meet it only at a joint. For blocks sharing exactly
one joint, all cross edges are therefore between the two remaining joints.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- An outside edge can enter a block only at one of its two joints. -/
theorem block_entry_is_joint (hM : M.IsMolecule) {S : Finset V} {a b u z : V}
    (hB : M.IsBlock S a b) (hu : u ∉ S) (hz : z ∈ S) (hadj : M.Adj u z) : z = a ∨ z = b := by
  by_cases ha : z = a
  · exact Or.inl ha
  · by_cases hb : z = b
    · exact Or.inr hb
    · exact (hu (block_interior_adj_mem M hM hB hz ha hb (adj_symmetric M hadj))).elim

/-- A loop-free singleton has no internal incidences. -/
theorem degIn_singleton_eq_zero {a : V}
    (hloop : ∀ x, M.atom x = a → M.atom (M.mate x) ≠ a) : M.degIn {a} a = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxv,hxa,hxm⟩ := Finset.mem_filter.mp hx
  exact hloop x ((mem_dartsAt M a x).mp hxv) (Finset.mem_singleton.mp hxm)

/-- The shared joint has degree four in the union of connected blocks. -/
theorem concatenation_common_degree {A B : Finset V} {a b c : V}
    (hA : M.IsBlock A a c) (hB : M.IsBlock B b c) (hcA : GroupConnected M A)
    (hi : A ∩ B = {c}) : M.degIn (A ∪ B) c = 4 := by
  have hno : ∀ x, M.atom x = c → M.atom (M.mate x) ≠ c := by
    intro x hx
    have hh := connected_block_no_joint_loop M hA hcA (Or.inr hx)
    rw [hx] at hh
    exact hh
  have hdc : M.degIn (A ∩ B) c = 0 := by rw [hi]; exact degIn_singleton_eq_zero M hno
  have hs := degIn_union_add_inter M A B hA.2.2.1 hB.2.2.1
  have hdA := (block_joint_degrees M hA).2
  have hdB := (block_joint_degrees M hB).2
  omega

/-- Internal incidences at a remaining joint split into those in its own
block and the actual bonds joining the two remaining joints. -/
theorem concatenation_endpoint_degree (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (hA : M.IsBlock A a c) (hB : M.IsBlock B b c) (hi : A ∩ B = {c}) :
    M.degIn (A ∪ B) a = 2+M.bondsBetween a b := by
  classical
  have haB : a ∉ B := by
    intro haB
    have hh : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨hA.2.1,haB⟩
    rw [hi] at hh
    exact hA.2.2.2.1 (Finset.mem_singleton.mp hh)
  have hbA : b ∉ A := by
    intro hbA
    have hh : b ∈ A ∩ B := Finset.mem_inter.mpr ⟨hbA,hB.2.1⟩
    rw [hi] at hh
    exact hB.2.2.2.1 (Finset.mem_singleton.mp hh)
  have hab : a ≠ b := by intro he; exact haB (he.symm ▸ hB.2.1)
  let DA := (M.dartsAt a).filter (M.InGroup A)
  let DX := (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b)
  have he : (M.dartsAt a).filter (M.InGroup (A ∪ B)) = DA ∪ DX := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxv,hxu,hxm⟩ := Finset.mem_filter.mp hx
      have hxa := (mem_dartsAt M a x).mp hxv
      rcases Finset.mem_union.mp hxm with hma | hmb
      · exact Finset.mem_union_left DX (Finset.mem_filter.mpr ⟨hxv,hxa.symm ▸ hA.2.1,hma⟩)
      · have hadj : M.Adj a (M.atom (M.mate x)) := ⟨x,hxa,rfl⟩
        rcases block_entry_is_joint M hM hB haB hmb hadj with he | he
        · exact Finset.mem_union_right DA (Finset.mem_filter.mpr ⟨hxv,he⟩)
        · exact Finset.mem_union_left DX (Finset.mem_filter.mpr
            ⟨hxv,hxa.symm ▸ hA.2.1,he.symm ▸ hA.2.2.1⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxA | hxX
      · obtain ⟨hxv,hxa,hxm⟩ := Finset.mem_filter.mp hxA
        exact Finset.mem_filter.mpr ⟨hxv,Finset.mem_union_left B hxa,Finset.mem_union_left B hxm⟩
      · obtain ⟨hxv,hxm⟩ := Finset.mem_filter.mp hxX
        have hxa := (mem_dartsAt M a x).mp hxv
        exact Finset.mem_filter.mpr ⟨hxv,hxa.symm ▸ Finset.mem_union_left B hA.2.1,
          hxm.symm ▸ Finset.mem_union_right A hB.2.1⟩
  have hdis : Disjoint DA DX := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxX
    have hmA := (Finset.mem_filter.mp hxA).2.2
    have hmB := (Finset.mem_filter.mp hxX).2
    exact hbA (hmB ▸ hmA)
  unfold Molecule.degIn
  rw [he,Finset.card_union_of_disjoint hdis]
  change M.degIn A a+DX.card = _
  rw [(block_joint_degrees M hA).1,bondsBetween_eq_card_darts M hab]

/-- All atoms except the two remaining joints have degree four after
concatenation, including the common joint. -/
theorem concatenation_interior_degree (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (hA : M.IsBlock A a c) (hB : M.IsBlock B b c) (hcA : GroupConnected M A)
    (hi : A ∩ B = {c}) :
    ∀ z ∈ A ∪ B, z ≠ a → z ≠ b → M.degIn (A ∪ B) z = 4 := by
  intro z hz hza hzb
  by_cases hzc : z = c
  · subst z
    exact concatenation_common_degree M hA hB hcA hi
  · have hzM : z ∈ M.atoms :=
      (Finset.mem_union.mp hz).elim (fun hh => hA.1 hh) (fun hh => hB.1 hh)
    have hle := (degIn_le_deg M (A ∪ B) z).trans (deg_le_four M hM hzM)
    have hge : 4 ≤ M.degIn (A ∪ B) z := by
      rcases Finset.mem_union.mp hz with hzA | hzB
      · have h4 := hA.2.2.2.2.2.2.2.2.1 z hzA hza hzc
        have hm := degIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) z
        omega
      · have h4 := hB.2.2.2.2.2.2.2.2.1 z hzB hzb hzc
        have hm := degIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) z
        omega
    omega

/-- At most one bond can join the two remaining joints: two would create
a saturated atomic group, forbidden by the molecule axioms. -/
theorem concatenation_cross_bonds_le_one (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (hA : M.IsBlock A a c) (hB : M.IsBlock B b c) (hcA : GroupConnected M A)
    (hi : A ∩ B = {c}) : M.bondsBetween a b ≤ 1 := by
  have hdA := concatenation_endpoint_degree M hM hA hB hi
  have hdB := concatenation_endpoint_degree M hM hB hA (by rw [Finset.inter_comm,hi])
  rw [Finset.union_comm,bondsBetween_symm M b a] at hdB
  have haM := hA.1 hA.2.1
  have hle := (degIn_le_deg M (A ∪ B) a).trans (deg_le_four M hM haM)
  by_contra h
  have hs : M.bondsBetween a b = 2 := by omega
  have hfull : ∀ z ∈ A ∪ B, M.degIn (A ∪ B) z = 4 := by
    intro z hz
    by_cases ha : z = a
    · subst z
      omega
    · by_cases hb : z = b
      · subst z
        omega
      · exact concatenation_interior_degree M hM hA hB hcA hi z hz ha hb
  exact no_saturated_group M hM
    (by intro z hz; exact (Finset.mem_union.mp hz).elim (fun hh => hA.1 hh) (fun hh => hB.1 hh))
    ⟨c,Finset.mem_union_left B hA.2.2.1⟩ hfull

end WaveTurbulence.Mole
