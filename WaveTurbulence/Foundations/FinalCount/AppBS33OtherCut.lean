/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33CutReconstruction
public import WaveTurbulence.Foundations.FinalCount.AppBD33CutData
import Mathlib.Tactic

/-! # Both conserved boundary differences in the split 3S3 figure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33OtherSide {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) : Finset V :=
  appbS33Side r ∪ r.removedAtoms

theorem appb_s33_other_side_labels (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitGeometry M r) :
    r.vertex 1 ∈ appbS33OtherSide r ∧ r.vertex 2 ∈ appbS33OtherSide r ∧
      r.vertex 3 ∈ appbS33OtherSide r ∧ r.vertex 4 ∉ appbS33OtherSide r ∧
      r.vertex 5 ∈ appbS33OtherSide r ∧ r.vertex 6 ∉ appbS33OtherSide r := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_side_labels M r hgeom
  have hr (i : ℕ) (hi : i ∈ AppbPatternKind.s33.pattern.vertices) := r.vertex_mem_removed_iff i hi
  simp only [appbS33OtherSide,mem_union,h1,h2,h3,h4,h5,h6,false_or,true_or,true_and,
    hr 1 (by decide),hr 2 (by decide),hr 4 (by decide),hr 6 (by decide)]
  decide

noncomputable def appbS33OtherCutPair {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitGeometry M r) :
    AppbCutPair r (appbS33OtherSide r) where
  subset_atoms := Finset.union_subset (appbS33CutPair r hgeom).subset_atoms r.removedAtoms_subset
  crossing := r.union_removed_cut_crossing _ _ (fun _ h => h) (r.residual_cut_crossing (r.vertex 3))
  first := ⟨2,by decide⟩
  second := ⟨4,by decide⟩
  distinct := by decide
  first_cross := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_other_side_labels M r hgeom
    apply (r.edge_cut_cross_iff (appbS33OtherSide r) ⟨2,by decide⟩).mpr
    change ((r.vertex 1 ∈ appbS33OtherSide r ∧ r.vertex 4 ∉ appbS33OtherSide r) ∨
      (r.vertex 1 ∉ appbS33OtherSide r ∧ r.vertex 4 ∈ appbS33OtherSide r))
    simp [h1,h4]
  second_cross := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_other_side_labels M r hgeom
    apply (r.edge_cut_cross_iff (appbS33OtherSide r) ⟨4,by decide⟩).mpr
    change ((r.vertex 2 ∈ appbS33OtherSide r ∧ r.vertex 6 ∉ appbS33OtherSide r) ∨
      (r.vertex 2 ∉ appbS33OtherSide r ∧ r.vertex 6 ∈ appbS33OtherSide r))
    simp [h2,h6]
  other := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_other_side_labels M r hgeom
    intro i hi2 hi4
    fin_cases i
    · apply (r.edge_cut_same_iff (appbS33OtherSide r) ⟨0,by decide⟩).mpr
      change (r.vertex 1 ∈ appbS33OtherSide r ↔ r.vertex 2 ∈ appbS33OtherSide r)
      simp only [h1,h2]
    · apply (r.edge_cut_same_iff (appbS33OtherSide r) ⟨1,by decide⟩).mpr
      change (r.vertex 1 ∈ appbS33OtherSide r ↔ r.vertex 3 ∈ appbS33OtherSide r)
      simp only [h1,h3]
    · exact False.elim (hi2 rfl)
    · apply (r.edge_cut_same_iff (appbS33OtherSide r) ⟨3,by decide⟩).mpr
      change (r.vertex 2 ∈ appbS33OtherSide r ↔ r.vertex 5 ∈ appbS33OtherSide r)
      simp only [h2,h5]
    · exact False.elim (hi4 rfl)

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem edge_atom_mem_side_iff_fst (S : Finset V) (i : Fin P.edges.length)
    (hf : r.vertex P.edges[i].1 ∈ S) (hs : r.vertex P.edges[i].2 ∉ S) :
    M.atom (r.edge i).val ∈ S ↔ M.atom (r.edge i).val = r.vertex P.edges[i].1 := by
  have hne : r.vertex P.edges[i].2 ≠ r.vertex P.edges[i].1 := fun h => hs (h.symm ▸ hf)
  rcases Sym2.eq_iff.mp (r.endpoints i) with h | h
  · simp only [h.1,hf,iff_true]
  · simp only [h.1,hs,hne]

theorem edge_atom_mem_side_iff_ne_fst (S : Finset V) (i : Fin P.edges.length)
    (hf : r.vertex P.edges[i].1 ∉ S) (hs : r.vertex P.edges[i].2 ∈ S) :
    M.atom (r.edge i).val ∈ S ↔ M.atom (r.edge i).val ≠ r.vertex P.edges[i].1 := by
  have hne : r.vertex P.edges[i].2 ≠ r.vertex P.edges[i].1 := fun h => hf (h ▸ hs)
  rcases Sym2.eq_iff.mp (r.endpoints i) with h | h
  · simp only [h.1,hf,ne_eq,not_true_eq_false]
  · simp only [h.1,hs,true_iff]
    exact hne

end AppbRealization
end WaveTurbulence.Mole
