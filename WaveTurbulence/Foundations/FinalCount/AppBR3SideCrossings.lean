/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCrossingDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
public import WaveTurbulence.Foundations.FinalCount.AppBEdgeCutTables
import Mathlib.Tactic

/-! # Star bonds entering the two sides of a residual special bridge -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_deleted_crossing_card_pos_of_singleton (M : Molecule V D) (Y S : Finset V)
    (e : Degen.RetainedDart M Y)
    (he : appbCrossingBonds (Degen.eraseAtoms M Y) S = {e})
    (hb : ∀ x : D,¬Degen.IsBridge M x) :
    0 < (appbCrossingBonds M S ∩ appbRemovedBonds M Y).card := by
  have hd := appb_crossing_eraseAtoms_decomposition M Y S
  have hdis := appb_crossing_deleted_retained_disjoint M Y S
  rw [he,image_singleton] at hd hdis
  have hc := congrArg Finset.card hd
  rw [card_union_of_disjoint hdis,card_singleton] at hc
  have hn := appb_crossing_card_ne_one M S hb
  omega

private theorem mem_crossing (M : Molecule V D) (S : Finset V) (x : D) :
    x ∈ appbCrossingBonds M S ↔ x ∈ M.bonds ∧
      ((M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S) ∨ (M.atom x ∉ S ∧ M.atom (M.mate x) ∈ S)) := by
  simp only [appbCrossingBonds,mem_filter]

theorem appb_r3_other_mem_post {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern) (j : Fin AppbPatternKind.r3.pattern.edges.length) :
    r.vertex (2+j.val) ∈ r.post.atoms := by
  fin_cases j
  all_goals exact r.vertex_mem_post _ (by decide) (by decide)

theorem appb_r3_cross_iff_other_mem {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern) (S : Finset V) (hS : S ⊆ r.post.atoms)
    (j : Fin AppbPatternKind.r3.pattern.edges.length) :
    (r.edge j).val ∈ appbCrossingBonds M S ↔ r.vertex (2+j.val) ∈ S := by
  have hv : r.vertex 1 ∉ S := by
    intro hv
    exact (mem_sdiff.mp (hS hv)).2 (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.r3.pattern.removed by decide))
  have hb := (mem_filter.mp (r.edge j).property).1
  rw [mem_crossing,and_iff_right hb,r.edge_cut_cross_iff]
  fin_cases j
  · change ((r.vertex 1 ∈ S ∧ r.vertex 2 ∉ S) ∨ (r.vertex 1 ∉ S ∧ r.vertex 2 ∈ S)) ↔ r.vertex 2 ∈ S
    simp only [hv,not_false_eq_true,false_and,true_and,false_or]
  · change ((r.vertex 1 ∈ S ∧ r.vertex 3 ∉ S) ∨ (r.vertex 1 ∉ S ∧ r.vertex 3 ∈ S)) ↔ r.vertex 3 ∈ S
    simp only [hv,not_false_eq_true,false_and,true_and,false_or]
  · change ((r.vertex 1 ∈ S ∧ r.vertex 4 ∉ S) ∨ (r.vertex 1 ∉ S ∧ r.vertex 4 ∈ S)) ↔ r.vertex 4 ∈ S
    simp only [hv,not_false_eq_true,false_and,true_and,false_or]

theorem appb_r3_cross_complement_iff {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern) (S : Finset V) (hS : S ⊆ r.post.atoms)
    {x : D} (hx : x ∈ appbRemovedBonds M r.removedAtoms) :
    x ∈ appbCrossingBonds M S ↔ x ∉ appbCrossingBonds M (r.post.atoms \ S) := by
  obtain ⟨j,hj⟩ := r.edge.surjective ⟨x,hx⟩
  have he : (r.edge j).val = x := congrArg Subtype.val hj
  rw [← he,appb_r3_cross_iff_other_mem r S hS,
    appb_r3_cross_iff_other_mem r (r.post.atoms \ S) sdiff_subset]
  simp only [mem_sdiff,appb_r3_other_mem_post r j,true_and,not_not]

end WaveTurbulence.Mole
