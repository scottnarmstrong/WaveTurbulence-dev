/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBoundaryCounts
import Mathlib.Tactic

/-! # Actual cut bonds split into deleted and retained physical bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_crossing_complement (M : Molecule V D) (S : Finset V) :
    appbCrossingBonds M (M.atoms \ S) = appbCrossingBonds M S := by
  ext x
  simp only [appbCrossingBonds,mem_filter,mem_sdiff,M.atom_mem,true_and]
  tauto

theorem appb_crossing_eraseAtoms_decomposition (M : Molecule V D) (Y S : Finset V) :
    appbCrossingBonds M S = (appbCrossingBonds M S ∩ appbRemovedBonds M Y) ∪
      ((appbCrossingBonds (Degen.eraseAtoms M Y) S).image Subtype.val) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hb,ht⟩ := mem_filter.mp hx
    by_cases hd : x ∈ appbRemovedBonds M Y
    · exact mem_union_left _ (mem_inter.mpr ⟨hx,hd⟩)
    · have hn : M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y := by
        constructor
        · intro h
          exact hd (mem_filter.mpr ⟨hb,Or.inl h⟩)
        · intro h
          exact hd (mem_filter.mpr ⟨hb,Or.inr h⟩)
      let xr : Degen.RetainedDart M Y := ⟨x,hn⟩
      have hr : xr ∈ appbCrossingBonds (Degen.eraseAtoms M Y) S :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hb).2⟩,ht⟩
      exact mem_union_right _ (mem_image.mpr ⟨xr,hr,rfl⟩)
  · intro hx
    rcases mem_union.mp hx with hx | hx
    · exact (mem_inter.mp hx).1
    · obtain ⟨xr,hr,rfl⟩ := mem_image.mp hx
      obtain ⟨hb,ht⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hb).2⟩,ht⟩

theorem appb_crossing_deleted_retained_disjoint (M : Molecule V D) (Y S : Finset V) :
    Disjoint (appbCrossingBonds M S ∩ appbRemovedBonds M Y)
      ((appbCrossingBonds (Degen.eraseAtoms M Y) S).image Subtype.val) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hd := (mem_filter.mp (mem_inter.mp hx).2).2
  obtain ⟨xr,hr,he⟩ := mem_image.mp hy
  rw [← he] at hd
  exact hd.elim xr.property.1 xr.property.2

theorem appb_crossing_card_ne_one (M : Molecule V D) (S : Finset V)
    (hb : ∀ e : D,¬Degen.IsBridge M e) : (appbCrossingBonds M S).card ≠ 1 := by
  intro h
  have hc : (Degen.boundaryDarts M S).card = 1 := (appb_boundary_card M S).trans h
  obtain ⟨e,he⟩ := card_eq_one.mp hc
  exact hb e (Degen.isBridge_of_single_boundary M S he)

end WaveTurbulence.Mole
