/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33OtherCut
import Mathlib.Tactic

/-! # Actual opposite cut signs in both split 3S3 boundary pairs -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_cut_signs_opposite (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitGeometry M r) :
    appbCutSign M (appbS33Side r) (r.edge ⟨1,by decide⟩).val ≠
      appbCutSign M (appbS33Side r) (r.edge ⟨3,by decide⟩).val := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_side_labels M r hgeom
  have hm1 := r.edge_atom_mem_side_iff_ne_fst (appbS33Side r) ⟨1,by decide⟩ h1 h3
  have hm3 := r.edge_atom_mem_side_iff_ne_fst (appbS33Side r) ⟨3,by decide⟩ h2 h5
  change (M.atom (r.edge ⟨1,by decide⟩).val ∈ appbS33Side r ↔ M.atom (r.edge ⟨1,by decide⟩).val ≠ r.vertex 1) at hm1
  change (M.atom (r.edge ⟨3,by decide⟩).val ∈ appbS33Side r ↔ M.atom (r.edge ⟨3,by decide⟩).val ≠ r.vertex 2) at hm3
  have ho := hgeom.2.2.2.1
  unfold AppbOppositeFrom at ho
  by_cases ha : M.atom (r.edge ⟨1,by decide⟩).val = r.vertex 1 <;>
    by_cases hb : M.atom (r.edge ⟨3,by decide⟩).val = r.vertex 2
  all_goals simp_all [appbCutSign]

theorem appb_s33_other_cut_signs_opposite (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitGeometry M r) :
    appbCutSign M (appbS33OtherSide r) (r.edge ⟨2,by decide⟩).val ≠
      appbCutSign M (appbS33OtherSide r) (r.edge ⟨4,by decide⟩).val := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_other_side_labels M r hgeom
  have hm2 := r.edge_atom_mem_side_iff_fst (appbS33OtherSide r) ⟨2,by decide⟩ h1 h4
  have hm4 := r.edge_atom_mem_side_iff_fst (appbS33OtherSide r) ⟨4,by decide⟩ h2 h6
  change (M.atom (r.edge ⟨2,by decide⟩).val ∈ appbS33OtherSide r ↔ M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 1) at hm2
  change (M.atom (r.edge ⟨4,by decide⟩).val ∈ appbS33OtherSide r ↔ M.atom (r.edge ⟨4,by decide⟩).val = r.vertex 2) at hm4
  have ho := hgeom.2.2.2.2
  unfold AppbOppositeFrom at ho
  by_cases ha : M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 1 <;>
    by_cases hb : M.atom (r.edge ⟨4,by decide⟩).val = r.vertex 2
  all_goals simp_all [appbCutSign]

end WaveTurbulence.Mole
