/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD336SplitSide
import Mathlib.Tactic

/-! # The exact two-bond cut in the four-circuit branch of 3D3-6G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbD336CutPair {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33new.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hF : r.post.numComponents = 2) :
    AppbCutPair r (appbD336SplitSide r) where
  subset_atoms := union_subset (by
    intro v hv
    exact ((Degen.mem_residualComponent M r.removedAtoms (r.vertex 5) v).mp hv).1)
    (singleton_subset_iff.mpr (r.vertex_mem 3 (by decide)))
  crossing := r.union_removed_cut_crossing _ _ (by
    intro v hv
    have he := mem_singleton.mp hv
    subst v
    exact mem_image_of_mem _ (show 3 ∈ AppbPatternKind.d33new.pattern.removed by decide))
    (r.residual_cut_crossing (r.vertex 5))
  first := ⟨2,by decide⟩
  second := ⟨4,by decide⟩
  distinct := by decide
  first_cross := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_d336_split_side_labels M r hc hF
    apply (r.edge_cut_cross_iff (appbD336SplitSide r) ⟨2,by decide⟩).mpr
    change ((r.vertex 1 ∈ appbD336SplitSide r ∧ r.vertex 3 ∉ appbD336SplitSide r) ∨
      (r.vertex 1 ∉ appbD336SplitSide r ∧ r.vertex 3 ∈ appbD336SplitSide r))
    simp only [h1,h3,not_false_eq_true,not_true_eq_false,true_and,false_and,and_true,and_false,true_or,or_true,false_or,or_false]
  second_cross := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_d336_split_side_labels M r hc hF
    apply (r.edge_cut_cross_iff (appbD336SplitSide r) ⟨4,by decide⟩).mpr
    change ((r.vertex 3 ∈ appbD336SplitSide r ∧ r.vertex 4 ∉ appbD336SplitSide r) ∨
      (r.vertex 3 ∉ appbD336SplitSide r ∧ r.vertex 4 ∈ appbD336SplitSide r))
    simp only [h3,h4,not_false_eq_true,not_true_eq_false,true_and,false_and,and_true,and_false,true_or,or_true,false_or,or_false]
  other := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_d336_split_side_labels M r hc hF
    intro i hi2 hi4
    fin_cases i
    · apply (r.edge_cut_same_iff (appbD336SplitSide r) ⟨0,by decide⟩).mpr
      change (r.vertex 1 ∈ appbD336SplitSide r ↔ r.vertex 2 ∈ appbD336SplitSide r)
      simp only [h1,h2]
    · apply (r.edge_cut_same_iff (appbD336SplitSide r) ⟨1,by decide⟩).mpr
      change (r.vertex 1 ∈ appbD336SplitSide r ↔ r.vertex 2 ∈ appbD336SplitSide r)
      simp only [h1,h2]
    · exact False.elim (hi2 rfl)
    · apply (r.edge_cut_same_iff (appbD336SplitSide r) ⟨3,by decide⟩).mpr
      change (r.vertex 2 ∈ appbD336SplitSide r ↔ r.vertex 4 ∈ appbD336SplitSide r)
      simp only [h2,h4]
    · exact False.elim (hi4 rfl)
    · apply (r.edge_cut_same_iff (appbD336SplitSide r) ⟨5,by decide⟩).mpr
      change (r.vertex 3 ∈ appbD336SplitSide r ↔ r.vertex 5 ∈ appbD336SplitSide r)
      simp only [h3,h5]
    · apply (r.edge_cut_same_iff (appbD336SplitSide r) ⟨6,by decide⟩).mpr
      change (r.vertex 3 ∈ appbD336SplitSide r ↔ r.vertex 5 ∈ appbD336SplitSide r)
      simp only [h3,h5]
    · apply (r.edge_cut_same_iff (appbD336SplitSide r) ⟨7,by decide⟩).mpr
      change (r.vertex 4 ∈ appbD336SplitSide r ↔ r.vertex 6 ∈ appbD336SplitSide r)
      simp only [h4,h6]
    · apply (r.edge_cut_same_iff (appbD336SplitSide r) ⟨8,by decide⟩).mpr
      change (r.vertex 4 ∈ appbD336SplitSide r ↔ r.vertex 6 ∈ appbD336SplitSide r)
      simp only [h4,h6]

end WaveTurbulence.Mole
