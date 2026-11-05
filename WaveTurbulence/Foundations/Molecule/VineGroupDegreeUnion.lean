/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBlockSeparator
public import WaveTurbulence.Foundations.Molecule.VineBlockBalance
public import WaveTurbulence.Foundations.Molecule.VineJointFlows
import Mathlib.Tactic

/-! # Degree lower bounds for two groups meeting at a loop-free joint -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The internal dart families of two atomic groups sharing only a
loop-free atom are disjoint, including their oriented subfamilies. -/
theorem group_filtered_card_union_le (M : Molecule V D) {S T : Finset V} {b : V}
    (hST : S ∩ T={b}) (hloop : ¬M.Adj b b) (v : V) (P : D → Prop) [DecidablePred P] :
    ((M.dartsAt v).filter (fun d => M.InGroup S d ∧ P d)).card+
      ((M.dartsAt v).filter (fun d => M.InGroup T d ∧ P d)).card ≤
      ((M.dartsAt v).filter (fun d => M.InGroup (S ∪ T) d ∧ P d)).card := by
  classical
  let F := fun A => (M.dartsAt v).filter (fun d => M.InGroup A d ∧ P d)
  have hdis : Disjoint (F S) (F T) := by
    apply disjoint_left.mpr
    intro d hdS hdT
    have hs := (mem_filter.mp hdS).2.1
    have ht := (mem_filter.mp hdT).2.1
    have ha : M.atom d=b := mem_singleton.mp (hST ▸ mem_inter.mpr ⟨hs.1,ht.1⟩)
    have hb : M.atom (M.mate d)=b := mem_singleton.mp (hST ▸ mem_inter.mpr ⟨hs.2,ht.2⟩)
    exact hloop ⟨d,ha,hb⟩
  have hsub : F S ∪ F T ⊆ F (S ∪ T) := by
    intro d hd
    rcases mem_union.mp hd with hd | hd
    · obtain ⟨hdv,⟨hu,hv⟩,hp⟩ := mem_filter.mp hd
      exact mem_filter.mpr ⟨hdv,⟨mem_union_left _ hu,mem_union_left _ hv⟩,hp⟩
    · obtain ⟨hdv,⟨hu,hv⟩,hp⟩ := mem_filter.mp hd
      exact mem_filter.mpr ⟨hdv,⟨mem_union_right _ hu,mem_union_right _ hv⟩,hp⟩
  have hh := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hh
  exact hh

/-- Restricted outgoing and incoming degrees are monotone in the atom group. -/
theorem oriented_degree_mono (M : Molecule V D) {S T : Finset V} (hST : S ⊆ T) (v : V) :
    M.outIn S v ≤ M.outIn T v ∧ M.inIn S v ≤ M.inIn T v := by
  constructor
  · apply card_le_card
    intro d hd
    obtain ⟨hdv,⟨hu,hv⟩,ho⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨hdv,⟨hST hu,hST hv⟩,ho⟩
  · apply card_le_card
    intro d hd
    obtain ⟨hdv,⟨hu,hv⟩,ho⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨hdv,⟨hST hu,hST hv⟩,ho⟩

/-- Unoriented internal degrees add as a lower bound when the intersection
contains no bond, since every old internal dart survives in the union. -/
theorem degIn_add_le_union (M : Molecule V D) {S T : Finset V} {b : V}
    (hST : S ∩ T={b}) (hloop : ¬M.Adj b b) (v : V) :
    M.degIn S v+M.degIn T v ≤ M.degIn (S ∪ T) v := by
  simpa only [and_true,Molecule.degIn] using group_filtered_card_union_le M hST hloop v (fun _ => True)

end WaveTurbulence.Vine
