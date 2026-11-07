/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33TopologyReconstruction
public import WaveTurbulence.Foundations.FinalCount.AppBD33CutData
import Mathlib.Tactic

/-! # Both conserved boundary differences in the split 3S3 figure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33TopologyOtherSide {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) : Finset V :=
  appbS33Side r ∪ r.removedAtoms

theorem appb_s33_topology_other_side_labels (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitTopology M r) :
    r.vertex 1 ∈ appbS33TopologyOtherSide r ∧ r.vertex 2 ∈ appbS33TopologyOtherSide r ∧
      r.vertex 3 ∈ appbS33TopologyOtherSide r ∧ r.vertex 4 ∉ appbS33TopologyOtherSide r ∧
      r.vertex 5 ∈ appbS33TopologyOtherSide r ∧ r.vertex 6 ∉ appbS33TopologyOtherSide r := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_side_labels_topology M r hgeom
  have hr (i : ℕ) (hi : i ∈ AppbPatternKind.s33.pattern.vertices) := r.vertex_mem_removed_iff i hi
  simp only [appbS33TopologyOtherSide,mem_union,h1,h2,h3,h4,h5,h6,false_or,true_or,true_and,
    hr 1 (by decide),hr 2 (by decide),hr 4 (by decide),hr 6 (by decide)]
  decide

noncomputable def appbS33TopologyOtherCutPair {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitTopology M r) :
    AppbCutPair r (appbS33TopologyOtherSide r) where
  subset_atoms := Finset.union_subset (appbS33TopologyCutPair r hgeom).subset_atoms r.removedAtoms_subset
  crossing := r.union_removed_cut_crossing _ _ (fun _ h => h) (r.residual_cut_crossing (r.vertex 3))
  first := ⟨2,by decide⟩
  second := ⟨4,by decide⟩
  distinct := by decide
  first_cross := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_topology_other_side_labels M r hgeom
    apply (r.edge_cut_cross_iff (appbS33TopologyOtherSide r) ⟨2,by decide⟩).mpr
    change ((r.vertex 1 ∈ appbS33TopologyOtherSide r ∧ r.vertex 4 ∉ appbS33TopologyOtherSide r) ∨
      (r.vertex 1 ∉ appbS33TopologyOtherSide r ∧ r.vertex 4 ∈ appbS33TopologyOtherSide r))
    simp [h1,h4]
  second_cross := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_topology_other_side_labels M r hgeom
    apply (r.edge_cut_cross_iff (appbS33TopologyOtherSide r) ⟨4,by decide⟩).mpr
    change ((r.vertex 2 ∈ appbS33TopologyOtherSide r ∧ r.vertex 6 ∉ appbS33TopologyOtherSide r) ∨
      (r.vertex 2 ∉ appbS33TopologyOtherSide r ∧ r.vertex 6 ∈ appbS33TopologyOtherSide r))
    simp [h2,h6]
  other := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_topology_other_side_labels M r hgeom
    intro i hi2 hi4
    fin_cases i
    · apply (r.edge_cut_same_iff (appbS33TopologyOtherSide r) ⟨0,by decide⟩).mpr
      change (r.vertex 1 ∈ appbS33TopologyOtherSide r ↔ r.vertex 2 ∈ appbS33TopologyOtherSide r)
      simp only [h1,h2]
    · apply (r.edge_cut_same_iff (appbS33TopologyOtherSide r) ⟨1,by decide⟩).mpr
      change (r.vertex 1 ∈ appbS33TopologyOtherSide r ↔ r.vertex 3 ∈ appbS33TopologyOtherSide r)
      simp only [h1,h3]
    · exact False.elim (hi2 rfl)
    · apply (r.edge_cut_same_iff (appbS33TopologyOtherSide r) ⟨3,by decide⟩).mpr
      change (r.vertex 2 ∈ appbS33TopologyOtherSide r ↔ r.vertex 5 ∈ appbS33TopologyOtherSide r)
      simp only [h2,h5]
    · exact False.elim (hi4 rfl)

end WaveTurbulence.Mole
