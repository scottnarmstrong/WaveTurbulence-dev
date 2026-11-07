/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR3SideCrossings
import Mathlib.Tactic

/-! # The three removed star bonds partition between the two residual sides -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_r3_side_crossing_card_sum {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern) (S : Finset V) (hS : S ⊆ r.post.atoms) :
    (appbCrossingBonds M S ∩ appbRemovedBonds M r.removedAtoms).card+
      (appbCrossingBonds M (r.post.atoms \ S) ∩ appbRemovedBonds M r.removedAtoms).card = 3 := by
  classical
  let A := appbCrossingBonds M S ∩ appbRemovedBonds M r.removedAtoms
  let B := appbCrossingBonds M (r.post.atoms \ S) ∩ appbRemovedBonds M r.removedAtoms
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hx hy
    exact ((appb_r3_cross_complement_iff r S hS (mem_inter.mp hx).2).mp (mem_inter.mp hx).1) (mem_inter.mp hy).1
  have hu : A ∪ B = appbRemovedBonds M r.removedAtoms := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_inter.mp hx).2
      · exact (mem_inter.mp hx).2
    · intro hx
      by_cases hs : x ∈ appbCrossingBonds M S
      · exact mem_union_left _ (mem_inter.mpr ⟨hs,hx⟩)
      · have ht : x ∈ appbCrossingBonds M (r.post.atoms \ S) := by
          by_contra hn
          exact hs ((appb_r3_cross_complement_iff r S hS hx).mpr hn)
        exact mem_union_right _ (mem_inter.mpr ⟨ht,hx⟩)
  have hc : (appbRemovedBonds M r.removedAtoms).card = 3 := by
    have hh := Fintype.card_congr r.edge
    change Fintype.card (Fin 3) = Fintype.card ↥(appbRemovedBonds M r.removedAtoms) at hh
    simpa only [Fintype.card_fin,Fintype.card_coe] using hh.symm
  change A.card+B.card = 3
  rw [← card_union_of_disjoint hdis,hu,hc]

end WaveTurbulence.Mole
