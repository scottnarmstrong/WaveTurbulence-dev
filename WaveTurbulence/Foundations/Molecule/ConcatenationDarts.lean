/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeConnectedBlocks
public import WaveTurbulence.Foundations.Molecule.MoleculeSingleDeficit
import Mathlib.Tactic

/-! # Exact internal-bond cover for legal block concatenations
TARGET `defblock`, `blockchainprop`: when the union is a block, every
internal bond belongs to an ingredient, and no bond belongs to both.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

theorem concatenation_internal_iff (hM : M.IsMolecule)
    {A B : Finset V} {a b c : V} (hA : M.IsBlock A a c) (hB : M.IsBlock B b c)
    (hU : M.IsBlock (A ∪ B) a b) (x : D) :
    M.InGroup (A ∪ B) x ↔ M.InGroup A x ∨ M.InGroup B x := by
  have hda := (block_joint_degrees M hA).1.trans (block_joint_degrees M hU).1.symm
  have hdb := (block_joint_degrees M hB).1.trans (block_joint_degrees M hU).2.symm
  have henda : M.atom x = a → M.InGroup (A ∪ B) x → M.InGroup A x := by
    intro hx hi
    have hm : x ∈ (M.dartsAt a).filter (M.InGroup (A ∪ B)) :=
      mem_filter.mpr ⟨(mem_dartsAt M a x).mpr hx,hi⟩
    rw [← internal_darts_eq_of_degree_eq M (subset_union_left : A ⊆ A ∪ B) a hda] at hm
    exact (mem_filter.mp hm).2
  have hendb : M.atom x = b → M.InGroup (A ∪ B) x → M.InGroup B x := by
    intro hx hi
    have hm : x ∈ (M.dartsAt b).filter (M.InGroup (A ∪ B)) :=
      mem_filter.mpr ⟨(mem_dartsAt M b x).mpr hx,hi⟩
    rw [← internal_darts_eq_of_degree_eq M (subset_union_right : B ⊆ A ∪ B) b hdb] at hm
    exact (mem_filter.mp hm).2
  constructor
  · intro hi
    rcases mem_union.mp hi.1 with hxA | hxB
    · by_cases hmA : M.atom (M.mate x) ∈ A
      · exact Or.inl ⟨hxA,hmA⟩
      · have hmB := (mem_union.mp hi.2).resolve_left hmA
        by_cases hxc : M.atom x = c
        · exact Or.inr ⟨hxc.symm ▸ hB.2.2.1,hmB⟩
        by_cases hxa : M.atom x = a
        · exact Or.inl (henda hxa hi)
        · exact (hmA (block_interior_adj_mem M hM hA hxA hxa hxc ⟨x,rfl,rfl⟩)).elim
    · by_cases hmB : M.atom (M.mate x) ∈ B
      · exact Or.inr ⟨hxB,hmB⟩
      · have hmA := (mem_union.mp hi.2).resolve_right hmB
        by_cases hxc : M.atom x = c
        · exact Or.inl ⟨hxc.symm ▸ hA.2.2.1,hmA⟩
        by_cases hxb : M.atom x = b
        · exact Or.inr (hendb hxb hi)
        · exact (hmB (block_interior_adj_mem M hM hB hxB hxb hxc ⟨x,rfl,rfl⟩)).elim
  · rintro (hi | hi)
    · exact ⟨mem_union_left _ hi.1,mem_union_left _ hi.2⟩
    · exact ⟨mem_union_right _ hi.1,mem_union_right _ hi.2⟩

theorem concatenation_internal_disjoint {A B : Finset V} {a c : V}
    (hA : M.IsBlock A a c) (hcA : GroupConnected M A) (hi : A ∩ B = {c}) (x : D) :
    ¬ (M.InGroup A x ∧ M.InGroup B x) := by
  rintro ⟨hxA,hxB⟩
  have hx : M.atom x = c := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hxA.1,hxB.1⟩)
  have hm : M.atom (M.mate x) = c := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hxA.2,hxB.2⟩)
  exact (connected_block_no_joint_loop M hA hcA (Or.inr hx)) (hm.trans hx.symm)

end WaveTurbulence.Mole
