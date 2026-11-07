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

def appbD33Frame {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33.pattern) :
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

def appbD33CutPair {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33.pattern) :
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
    change ((r.vertex 2 ∈ r.removedAtoms ∧ r.vertex 4 ∉ r.removedAtoms) ∨
      (r.vertex 2 ∉ r.removedAtoms ∧ r.vertex 4 ∈ r.removedAtoms))
    rw [r.vertex_mem_removed_iff 2 (by decide),r.vertex_mem_removed_iff 4 (by decide)]
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

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem edge_atom_mem_removed_iff_fst (i : Fin P.edges.length)
    (hf : P.edges[i].1 ∈ P.removed) (hs : P.edges[i].2 ∉ P.removed) :
    M.atom (r.edge i).val ∈ r.removedAtoms ↔ M.atom (r.edge i).val = r.vertex P.edges[i].1 := by
  have h1 : r.vertex P.edges[i].1 ∈ r.removedAtoms := mem_image_of_mem _ hf
  have h2 : r.vertex P.edges[i].2 ∉ r.removedAtoms :=
    fun h => hs ((r.vertex_mem_removed_iff _ (P.edge_snd_mem i)).mp h)
  have hne : r.vertex P.edges[i].2 ≠ r.vertex P.edges[i].1 := fun h => h2 (h.symm ▸ h1)
  rcases Sym2.eq_iff.mp (r.endpoints i) with h | h
  · simp only [h.1,h1,iff_true]
  · simp only [h.1,h2,hne]

end AppbRealization

/-- The operation's direction condition gives opposite cut signs. -/
theorem appb_d33_cut_signs_opposite (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) (hOpp : AppbD33BoundaryOpposite M r) :
    appbCutSign M r.removedAtoms (r.edge ⟨2,by decide⟩).val ≠
      appbCutSign M r.removedAtoms (r.edge ⟨3,by decide⟩).val := by
  have h2 := r.edge_atom_mem_removed_iff_fst ⟨2,by decide⟩ (by decide) (by decide)
  have h3 := r.edge_atom_mem_removed_iff_fst ⟨3,by decide⟩ (by decide) (by decide)
  change (M.atom (r.edge ⟨2,by decide⟩).val ∈ r.removedAtoms ↔ M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 1) at h2
  change (M.atom (r.edge ⟨3,by decide⟩).val ∈ r.removedAtoms ↔ M.atom (r.edge ⟨3,by decide⟩).val = r.vertex 2) at h3
  unfold AppbD33BoundaryOpposite AppbOppositeFrom at hOpp
  by_cases ha : M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 1 <;>
    by_cases hb : M.atom (r.edge ⟨3,by decide⟩).val = r.vertex 2
  all_goals simp_all [appbCutSign]

end WaveTurbulence.Mole
