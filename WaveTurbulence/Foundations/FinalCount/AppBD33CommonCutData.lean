/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPair
public import WaveTurbulence.Foundations.FinalCount.AppBEdgeCutTables
public import WaveTurbulence.Foundations.FinalCount.AppBTB2Reconstruction
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
public import WaveTurbulence.Foundations.FinalCount.AppBPatternMultiplicities
import Mathlib.Tactic

/-! # The exact two-boundary cut in a degree-three double pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbD33CommonFrame {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33same.pattern) :
    AppbTripleFrame r (r.vertex 1) where
  index := appbFirstThreeEmbedding _ (by decide)
  incidence := by
    intro j
    rw [r.edge_incidence _ 1 (by decide)]
    fin_cases j <;> decide
  other := by
    intro i hi
    rw [r.edge_incidence i 1 (by decide)]
    fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 2 rfl)
    · decide

def appbD33CommonCutPair {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33same.pattern) :
    AppbCutPair r r.removedAtoms where
  subset_atoms := r.removedAtoms_subset
  crossing := by
    intro x hx
    obtain ⟨hx,h⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hx,by rcases h with h | h; exact Or.inl h.1; exact Or.inr h.2⟩
  first := ⟨2,by decide⟩
  second := ⟨3,by decide⟩
  distinct := by decide
  first_cross := by
    apply (r.edge_cut_cross_iff r.removedAtoms ⟨2,by decide⟩).mpr
    change ((r.vertex 1 ∈ r.removedAtoms ∧ r.vertex 3 ∉ r.removedAtoms) ∨
      (r.vertex 1 ∉ r.removedAtoms ∧ r.vertex 3 ∈ r.removedAtoms))
    rw [r.vertex_mem_removed_iff 1 (by decide),r.vertex_mem_removed_iff 3 (by decide)]
    decide
  second_cross := by
    apply (r.edge_cut_cross_iff r.removedAtoms ⟨3,by decide⟩).mpr
    change ((r.vertex 2 ∈ r.removedAtoms ∧ r.vertex 3 ∉ r.removedAtoms) ∨
      (r.vertex 2 ∉ r.removedAtoms ∧ r.vertex 3 ∈ r.removedAtoms))
    rw [r.vertex_mem_removed_iff 2 (by decide),r.vertex_mem_removed_iff 3 (by decide)]
    decide
  other := by
    intro i hi2 hi3
    fin_cases i
    · apply (r.edge_cut_same_iff r.removedAtoms ⟨0,by decide⟩).mpr
      change (r.vertex 1 ∈ r.removedAtoms ↔ r.vertex 2 ∈ r.removedAtoms)
      rw [r.vertex_mem_removed_iff 1 (by decide),r.vertex_mem_removed_iff 2 (by decide)]
      decide
    · apply (r.edge_cut_same_iff r.removedAtoms ⟨1,by decide⟩).mpr
      change (r.vertex 1 ∈ r.removedAtoms ↔ r.vertex 2 ∈ r.removedAtoms)
      rw [r.vertex_mem_removed_iff 1 (by decide),r.vertex_mem_removed_iff 2 (by decide)]
      decide
    · exact False.elim (hi2 rfl)
    · exact False.elim (hi3 rfl)

end WaveTurbulence.Mole
