/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33SpecialNeighbors
public import WaveTurbulence.Foundations.FinalCount.AppBD33NeighborTable
import Mathlib.Tactic

/-! # Two consecutive normal double-pair steps have regular intermediate rails -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The next actual normal figure supplies the old neighbor-degree facts
needed to rule out special creation in the preceding step. -/
theorem consecutive_d33_no_new_special (M : Molecule V D) (hno : AppbNoLoops M)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (t : AppbRealization r.post AppbPatternKind.d33.pattern)
    (h1 : t.vertex 1 = r.vertex 3) (h2 : t.vertex 2 = r.vertex 4)
    (ht3 : r.post.deg (t.vertex 3) = 4) (ht4 : r.post.deg (t.vertex 4) = 4)
    (x : Degen.RetainedDart M r.removedAtoms) (hs : AppbSpecial r.post x) : AppbSpecial M x.val := by
  have h3not := (mem_sdiff.mp (r.vertex_mem_post 3 (by decide) (by decide))).2
  have h4not := (mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2
  have hdouble' := appb_d33_internal_multiplicity r.post t
  rw [h1,h2] at hdouble'
  have hdouble : M.bondsBetween (r.vertex 3) (r.vertex 4) = 2 :=
    (Degen.bondsBetween_erase_eq M r.removedAtoms h3not h4not).symm.trans hdouble'
  apply D33Special.no_new_special r hno hdouble ?_ x hs
  intro b hb hout hm
  have hbnot : b ∉ r.removedAtoms := by
    intro hi
    change b ∈ AppbPatternKind.d33.pattern.removed.image r.vertex at hi
    obtain ⟨i,hi,he⟩ := mem_image.mp hi
    exact hout (mem_image.mpr ⟨i,mem_union_left _ hi,he⟩)
  rcases hm with hm | hm
  · have hm' : r.post.bondsBetween (t.vertex 1) b = 1 := by
      rw [h1]
      exact (Degen.bondsBetween_erase_eq M r.removedAtoms h3not hbnot).trans hm
    have he := appb_d33_single_neighbor_1 r.post t b hm'
    have hd : M.deg b = 4 := by
      rw [← r.post_degree_outside b hout,he]
      exact ht3
    omega
  · have hm' : r.post.bondsBetween (t.vertex 2) b = 1 := by
      rw [h2]
      exact (Degen.bondsBetween_erase_eq M r.removedAtoms h4not hbnot).trans hm
    have he := appb_d33_single_neighbor_2 r.post t b hm'
    have hd : M.deg b = 4 := by
      rw [← r.post_degree_outside b hout,he]
      exact ht4
    omega

/-- Special-count nonincrease is derived by the actual outgoing-dart
inclusion, rather than a stored statistic assumption. -/
theorem consecutive_d33_special_count_le (M : Molecule V D) (hno : AppbNoLoops M)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (t : AppbRealization r.post AppbPatternKind.d33.pattern)
    (h1 : t.vertex 1 = r.vertex 3) (h2 : t.vertex 2 = r.vertex 4)
    (ht3 : r.post.deg (t.vertex 3) = 4) (ht4 : r.post.deg (t.vertex 4) = 4) :
    (appbSpecialBonds r.post).card ≤ (appbSpecialBonds M).card := by
  classical
  have hsub : (appbSpecialBonds r.post).image Subtype.val ⊆ appbSpecialBonds M := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact mem_filter.mpr ⟨mem_univ _,consecutive_d33_no_new_special M hno r t h1 h2 ht3 ht4 y (mem_filter.mp hy).2⟩
  calc
    _ = ((appbSpecialBonds r.post).image Subtype.val).card :=
      (card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ _ := card_le_card hsub

end WaveTurbulence.Mole.AppbAlgorithm
