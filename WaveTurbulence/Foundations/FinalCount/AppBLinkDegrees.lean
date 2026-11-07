/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinks
import Mathlib.Tactic

/-! # Low-degree vertices do not lie in selected ladder links -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Cardinality four exactly singles out selected length-one ladders. -/
theorem appb_link_iff_source_card (M : Molecule V D) (S : Finset V) :
    AppbLink M S ↔ Degen.SourceLadderSet M S ∧ S.card = 4 := by
  constructor
  · intro h
    exact ⟨h.sourceLadderSet,h.card⟩
  · rintro ⟨⟨m,u,v,h,rfl⟩,hc⟩
    have he := Degen.ladderAtoms_card_of_injective h.2.1
    have hm : m = 1 := by omega
    subst m
    exact ⟨u,v,h,rfl⟩

private theorem appb_ladder_u_degree_ge_three (M : Molecule V D) {m : ℕ}
    {u v : Fin (m+1) → V} (h : Degen.SourceLadder M u v) (j : Fin (m+1)) :
    3 ≤ M.deg (u j) := by
  obtain ⟨k,hkj,hrail⟩ := Degen.sourceLadder_u_single_neighbor M h j
  have hjv : u j ≠ v j := by
    intro he
    have hh := h.2.1 (show Sum.elim u v (.inl j) = Sum.elim u v (.inr j) from he)
    cases hh
  have hjk : u j ≠ u k := by
    intro he
    exact hkj (Sum.inl.inj (h.2.1 (show Sum.elim u v (.inl j) = Sum.elim u v (.inl k) from he))).symm
  have hvk : v j ≠ u k := by
    intro he
    have hh := h.2.1 (show Sum.elim u v (.inr j) = Sum.elim u v (.inl k) from he)
    cases hh
  have hnot : u j ∉ ({v j,u k} : Finset V) := by simp only [mem_insert,mem_singleton,not_or]; exact ⟨hjv,hjk⟩
  have hd := Degen.sum_neighbor_bonds_le_degree M (u j) {v j,u k} hnot
  rw [sum_pair hvk,h.2.2.2.1 j,hrail] at hd
  exact hd

/-- Every actual source-ladder atom has a double rung and a single rail. -/
theorem appb_source_ladder_degree_ge_three (M : Molecule V D) {S : Finset V}
    (h : Degen.SourceLadderSet M S) {a : V} (ha : a ∈ S) : 3 ≤ M.deg a := by
  obtain ⟨m,u,v,h,rfl⟩ := h
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    exact appb_ladder_u_degree_ge_three M h j
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    exact appb_ladder_u_degree_ge_three M (Degen.sourceLadder_swap M h) j

/-- Every link vertex has degree at least three, without a degree cap. -/
theorem AppbLink.degree_ge_three {M : Molecule V D} {S : Finset V} (h : AppbLink M S)
    {a : V} (ha : a ∈ S) : 3 ≤ M.deg a :=
  appb_source_ladder_degree_ge_three M h.sourceLadderSet ha

/-- In particular every degree-two deletion in Appendix B is disjoint
from every selected link. -/
theorem AppbLink.disjoint_low_degree {M : Molecule V D} {S Y : Finset V} (h : AppbLink M S)
    (hY : ∀ a ∈ Y, M.deg a ≤ 2) : Disjoint S Y := by
  apply disjoint_left.mpr
  intro a ha hya
  have h3 := h.degree_ge_three ha
  have h2 := hY a hya
  omega

/-- The double partner is also actual old graph data, not an assumed
property of a source operation. -/
theorem AppbLink.double_partner {M : Molecule V D} {S : Finset V} (h : AppbLink M S)
    {a : V} (ha : a ∈ S) : ∃ b ∈ M.atoms, a ≠ b ∧ M.bondsBetween a b = 2 := by
  obtain ⟨u,v,h,rfl⟩ := h
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    refine ⟨v j,(h.2.2.1 j).2,?_,h.2.2.2.1 j⟩
    intro he
    have hh := h.2.1 (show Sum.elim u v (.inl j) = Sum.elim u v (.inr j) from he)
    cases hh
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    refine ⟨u j,(h.2.2.1 j).1,?_,?_⟩
    · intro he
      have hh := h.2.1 (show Sum.elim u v (.inr j) = Sum.elim u v (.inl j) from he)
      cases hh
    · rw [Degen.bondsBetween_comm M]
      exact h.2.2.2.1 j

/-- Vertices with only single or triple incident multiplicities cannot
belong to any selected link. -/
theorem AppbLink.disjoint_no_double_partner {M : Molecule V D} {S Y : Finset V}
    (h : AppbLink M S)
    (hY : ∀ a ∈ Y, ∀ b ∈ M.atoms, a ≠ b → M.bondsBetween a b ≠ 2) : Disjoint S Y := by
  apply disjoint_left.mpr
  intro a ha hya
  obtain ⟨b,hb,hab,hd⟩ := h.double_partner ha
  exact hY a hya b hb hab hd

end WaveTurbulence.Mole
