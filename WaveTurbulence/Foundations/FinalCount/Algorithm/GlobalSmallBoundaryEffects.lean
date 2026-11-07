/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SmallBoundaryPaths
public import WaveTurbulence.Foundations.FinalCount.AppBBoundaryCounts
public import WaveTurbulence.Foundations.FinalCount.AppBPatternMultiplicities
import Mathlib.Tactic

/-! # Exact small-cut operation effects with untouched components present -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace FigurePaths
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem edge_path (i : Fin P.edges.length) :
    M.SameComponent (r.vertex P.edges[i].1) (r.vertex P.edges[i].2) := by
  rcases Sym2.eq_iff.mp (r.endpoints i) with h | h
  · exact Relation.EqvGen.rel _ _ ⟨(r.edge i).val,h⟩
  · exact Relation.EqvGen.rel _ _ ⟨M.mate (r.edge i).val,h.2,by rw [M.mate_mate]; exact h.1⟩

theorem removed_connected_of_center_incidence
    (hstar : ∀ a ∈ P.removed,a = 1 ∨ ∃ i : Fin P.edges.length,
      P.edges[i] = (1,a) ∨ P.edges[i] = (a,1)) :
    ∀ a ∈ r.removedAtoms,∀ b ∈ r.removedAtoms,M.SameComponent a b := by
  have hp (a : ℕ) (ha : a ∈ P.removed) : M.SameComponent (r.vertex 1) (r.vertex a) := by
    rcases hstar a ha with rfl | ⟨i,hi⟩
    · exact Relation.EqvGen.refl _
    · rcases hi with hi | hi
      · simpa only [hi] using edge_path r i
      · exact (show M.SameComponent (r.vertex a) (r.vertex 1) from by
          simpa only [hi] using edge_path r i).symm
  intro a ha b hb
  obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
  exact Relation.EqvGen.trans _ _ _ (hp i hi).symm (hp j hj)

end FigurePaths

theorem patterns_removed_center_incidence : ∀ k : AppbPatternKind,k ≠ .d33new →
      ∀ a ∈ k.pattern.removed,a = 1 ∨ ∃ i : Fin k.pattern.edges.length,
        k.pattern.edges[i] = (1,a) ∨ k.pattern.edges[i] = (a,1) := by
  intro k
  cases k <;> decide

theorem global_small_boundary_graph_effects (M : Molecule V D) (k : AppbPatternKind)
    (hk : k ≠ .d33new) (r : AppbRealization M k.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e)
    (hpos : 0 < k.pattern.boundaryCount) (hsmall : k.pattern.boundaryCount ≤ 3) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank-M.circuitRank = -(k.pattern.edges.length : ℤ)+k.pattern.removed.card ∧
    appbNu r.post-appbNu M = -4*(k.pattern.removed.card : ℤ)+2*k.pattern.edges.length := by
  have hbound : (Degen.boundaryDarts M r.removedAtoms).card ≤ 3 := by
    rw [r.boundary_card]; exact hsmall
  have hnon : (Degen.boundaryDarts M r.removedAtoms).Nonempty := card_pos.mp (by
    rw [r.boundary_card]; exact hpos)
  have hf := numComponents_eraseAtoms_eq_of_small_boundary M r.removedAtoms hbridge hbound hnon
    (FigurePaths.removed_connected_of_center_incidence r (patterns_removed_center_incidence k hk))
  have hf' : r.post.numComponents = M.numComponents := hf
  refine ⟨hf',?_,?_⟩
  · rw [r.post_circuitRank,hf']
    ring
  · rw [r.post_nu,hf']
    ring

end WaveTurbulence.Mole.AppbAlgorithm
