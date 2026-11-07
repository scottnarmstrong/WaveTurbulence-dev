/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainPrefixBlocks
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry

/-! # A source VC concatenation has no hidden cross bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open Finset RegRed
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A proper block union cannot retain a bond joining its two exterior
joints: such a bond would increase their defining internal degree two. -/
theorem block_concat_cross_count_zero (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} (hS : M.IsBlock S a b) (hT : M.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c) : M.bondsBetween a c = 0 := by
  have hS' := hS
  have hT' := hT
  have hU' := hU
  have he := Mole.concatenation_endpoint_degree M hM hS' (Mole.block_swap_joints M hT') hi
  have hd := (Mole.block_joint_degrees M hU').1
  omega

/-- All possible cross edges would join the two remaining joints, which
the proper union excludes. This is proved from the source block premises. -/
theorem block_concat_noCross (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} (hS : M.IsBlock S a b) (hT : M.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c) :
    ∀ x ∈ S, x ∉ T → ∀ y ∈ T, y ∉ S → ¬ M.Adj x y := by
  have hS' := hS
  have hT' := hT
  intro x hxS hxT y hyT hyS hxy
  have hy : y = c := by
    rcases Mole.block_entry_is_joint M hM hT' hxT hyT hxy with hy | hy
    · exact (hyS (hy ▸ hS'.2.2.1)).elim
    · exact hy
  have hx : x = a := by
    rcases Mole.block_entry_is_joint M hM hS' hyS hxS (Mole.adj_symmetric M hxy) with hx | hx
    · exact hx
    · exact (hxT (hx ▸ hT'.2.1)).elim
  subst x
  subst y
  have hz := block_concat_cross_count_zero M hM hS hT hi hU
  have hne := hU.2.2.2.1
  obtain ⟨e,he,hm⟩ := hxy
  have hp : 0 < M.bondsBetween a c := by
    rw [Mole.bondsBetween_eq_card_darts M hne]
    exact card_pos.mpr ⟨e,mem_filter.mpr ⟨(Mole.mem_dartsAt M a e).mpr he,hm⟩⟩
  omega

/-- Every internal bond of the full chain belongs to one of the two actual
pieces. No additional edge partition is assumed for chart gluing. -/
theorem block_concat_inGroup_iff (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} (hS : M.IsBlock S a b) (hT : M.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c) (e : D) :
    M.InGroup (S ∪ T) e ↔ M.InGroup S e ∨ M.InGroup T e := by
  constructor
  · rintro ⟨he,hm⟩
    rcases mem_union.mp he with he | he <;> rcases mem_union.mp hm with hm | hm
    · exact Or.inl ⟨he,hm⟩
    · by_cases ht : M.atom e ∈ T
      · exact Or.inr ⟨ht,hm⟩
      · by_cases hs : M.atom (M.mate e) ∈ S
        · exact Or.inl ⟨he,hs⟩
        · exact (block_concat_noCross M hM hS hT hi hU _ he ht _ hm hs ⟨e,rfl,rfl⟩).elim
    · by_cases hs : M.atom e ∈ S
      · exact Or.inl ⟨hs,hm⟩
      · by_cases ht : M.atom (M.mate e) ∈ T
        · exact Or.inr ⟨he,ht⟩
        · exact (block_concat_noCross M hM hS hT hi hU _ hm ht _ he hs
            (Mole.adj_symmetric M ⟨e,rfl,rfl⟩)).elim
    · exact Or.inr ⟨he,hm⟩
  · rintro (⟨he,hm⟩ | ⟨he,hm⟩)
    · exact ⟨mem_union_left _ he,mem_union_left _ hm⟩
    · exact ⟨mem_union_right _ he,mem_union_right _ hm⟩

end WaveTurbulence.VineEstS2
