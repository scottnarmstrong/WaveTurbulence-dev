/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.NewSpecialDeletion
public import WaveTurbulence.Foundations.FinalCount.Algorithm.PatternReachability
import Mathlib.Tactic

/-! # Component-local no-special tests for all transcribed figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem pattern_post_special_old_of_component_test (M : Molecule V D)
    (k : AppbPatternKind) (r : AppbRealization M k.pattern)
    (hn : ∀ x : Degen.RetainedDart M r.removedAtoms,
      M.SameComponent (r.vertex 1) (M.atom x.val) → ¬AppbSpecial r.post x)
    (x : Degen.RetainedDart M r.removedAtoms) (hs : AppbSpecial r.post x) : AppbSpecial M x.val := by
  have hp (a : ℕ) (ha : a ∈ k.pattern.vertices) :
      M.SameComponent (r.vertex 1) (r.vertex a) :=
    all_realized_vertices_connected M k r a ha
  have hsrc : M.atom x.val ∉ k.pattern.vertices.image r.vertex := by
    intro hi
    obtain ⟨a,ha,he⟩ := mem_image.mp hi
    exact hn x (he ▸ hp a ha) hs
  have htgt : M.atom (M.mate x.val) ∉ k.pattern.vertices.image r.vertex := by
    intro hi
    obtain ⟨a,ha,he⟩ := mem_image.mp hi
    have hpath : M.SameComponent (r.vertex 1) (M.atom (M.mate x.val)) := he ▸ hp a ha
    have hx : M.SameComponent (M.atom (M.mate x.val)) (M.atom x.val) :=
      Relation.EqvGen.rel _ _ ⟨M.mate x.val,rfl,by rw [M.mate_mate]⟩
    exact hn x (Relation.EqvGen.trans _ _ _ hpath hx) hs
  exact SpecialDeletion.old_of_endpoints_outside r x hsrc htgt hs

theorem pattern_special_count_le_of_component_test (M : Molecule V D)
    (k : AppbPatternKind) (r : AppbRealization M k.pattern)
    (hn : ∀ x : Degen.RetainedDart M r.removedAtoms,
      M.SameComponent (r.vertex 1) (M.atom x.val) → ¬AppbSpecial r.post x) :
    (appbSpecialBonds r.post).card ≤ (appbSpecialBonds M).card := by
  classical
  have hsub : (appbSpecialBonds r.post).image Subtype.val ⊆ appbSpecialBonds M := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact mem_filter.mpr ⟨mem_univ _,pattern_post_special_old_of_component_test M k r hn y (mem_filter.mp hy).2⟩
  calc
    _ = ((appbSpecialBonds r.post).image Subtype.val).card :=
      (card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ _ := card_le_card hsub

end WaveTurbulence.Mole.AppbAlgorithm
