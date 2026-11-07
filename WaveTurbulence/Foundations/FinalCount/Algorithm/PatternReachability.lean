/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.RealizedAdjacency
import Mathlib.Tactic

/-! # Every transcribed figure vertex is within three table edges of label one -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm

def PatternCenterReach (P : AppbPattern) (a : ℕ) : Prop :=
  a = 1 ∨
  (∃ i : Fin P.edges.length,P.edges[i].1 = 1 ∧ P.edges[i].2 = a) ∨
  (∃ i j : Fin P.edges.length,P.edges[i].1 = 1 ∧ P.edges[i].2 = P.edges[j].1 ∧ P.edges[j].2 = a) ∨
  (∃ i j l : Fin P.edges.length,P.edges[i].1 = 1 ∧ P.edges[i].2 = P.edges[j].1 ∧
    P.edges[j].2 = P.edges[l].1 ∧ P.edges[l].2 = a)

@[instance_reducible] instance (P : AppbPattern) (a : ℕ) : Decidable (PatternCenterReach P a) := by
  unfold PatternCenterReach
  infer_instance

theorem all_patterns_center_reach (k : AppbPatternKind) :
    ∀ a ∈ k.pattern.vertices,PatternCenterReach k.pattern a := by
  cases k <;> decide

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem realized_path_of_center_reach {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) {a : ℕ} (h : PatternCenterReach P a) :
    M.SameComponent (r.vertex 1) (r.vertex a) := by
  rcases h with rfl | ⟨i,hi1,hi2⟩ | ⟨i,j,hi1,hij,hj2⟩ | ⟨i,j,l,hi1,hij,hjl,hl2⟩
  · exact Relation.EqvGen.refl _
  · have hp := Relation.EqvGen.rel _ _ (realized_edge_adj r i)
    change Relation.EqvGen M.Adj _ _
    simpa only [hi1,hi2] using hp
  · have hp := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (realized_edge_adj r i))
      (show M.SameComponent (r.vertex P.edges[i].2) (r.vertex a) from by
        rw [hij,← hj2]
        exact Relation.EqvGen.rel _ _ (realized_edge_adj r j))
    change Relation.EqvGen M.Adj _ _
    simpa only [hi1] using hp
  · have hj := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (realized_edge_adj r j))
      (show M.SameComponent (r.vertex P.edges[j].2) (r.vertex a) from by
        rw [hjl,← hl2]
        exact Relation.EqvGen.rel _ _ (realized_edge_adj r l))
    have hp := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (realized_edge_adj r i))
      (show M.SameComponent (r.vertex P.edges[i].2) (r.vertex a) from by rw [hij]; exact hj)
    change Relation.EqvGen M.Adj _ _
    simpa only [hi1] using hp

theorem all_realized_vertices_connected (M : Molecule V D) (k : AppbPatternKind)
    (r : AppbRealization M k.pattern) (a : ℕ) (ha : a ∈ k.pattern.vertices) :
    M.SameComponent (r.vertex 1) (r.vertex a) :=
  realized_path_of_center_reach r (all_patterns_center_reach k a ha)

end WaveTurbulence.Mole.AppbAlgorithm
