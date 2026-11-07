/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSourceReinsertCaps
public import WaveTurbulence.Foundations.FinalCount.AppBS33ReinsertDegrees
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertAtoms
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertConnectivity
import Mathlib.Tactic

/-! # DH23 3S3-3G preserves both molecule axioms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_reinsert_isMolecule (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    (hdefect : ¬(M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 5) = 4)) :
    (r.directedPostWithBond 3 5 ⟨1,by decide⟩).IsMolecule := by
  classical
  let N := r.directedPostWithBond 3 5 ⟨1,by decide⟩
  have hatoms : N.atoms = r.post.atoms :=
    r.directedPostWithBond_atoms 3 5 ⟨1,by decide⟩ (by decide) (by decide) (by decide) (by decide)
  have hmem (j : ℕ) (hj : j ∈ ({3,4,5,6} : Finset ℕ)) : r.vertex j ∈ N.atoms := by
    rw [hatoms]
    have hjV : j ∈ AppbPatternKind.s33.pattern.vertices := by
      simp only [mem_insert,mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> decide
    have hjK : j ∉ AppbPatternKind.s33.pattern.removed := by
      simp only [mem_insert,mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> decide
    exact r.vertex_mem_post j hjV hjK
  have h3deg : N.deg (r.vertex 3) = M.deg (r.vertex 3) := by
    have hh := appb_s33_reinsert_survivor_degree M r 3 (by decide)
    norm_num at hh
    exact hh
  have h5deg : N.deg (r.vertex 5) = M.deg (r.vertex 5) := by
    have hh := appb_s33_reinsert_survivor_degree M r 5 (by decide)
    norm_num at hh
    exact hh
  have h4deg : N.deg (r.vertex 4)+1 = M.deg (r.vertex 4) := by
    have hh := appb_s33_reinsert_survivor_degree M r 4 (by decide)
    norm_num at hh
    exact hh
  have h4low : N.deg (r.vertex 4) ≠ 4 := by
    have hh := deg_le_four M hM (r.vertex_mem 4 (by decide))
    omega
  have hw : ∃ w ∈ N.atoms,N.SameComponent (r.vertex 3) w ∧ N.deg w ≠ 4 := by
    rcases not_and_or.mp hdefect with h3 | h5
    · exact ⟨r.vertex 3,hmem 3 (by decide),Relation.EqvGen.refl _,h3deg.trans_ne h3⟩
    · exact ⟨r.vertex 5,hmem 5 (by decide),
        r.sameComponent_directedPostWithBond 3 5 ⟨1,by decide⟩ hg.2.1,h5deg.trans_ne h5⟩
  refine ⟨appb_s33_reinsert_degree_caps hM r hg,?_⟩
  intro v hv
  rcases appb_twoComponents_reaches r.post hg.1 (hatoms ▸ hv) with h3 | h4
  · obtain ⟨w,hw,hpath,hdeg⟩ := hw
    exact ⟨w,hw,Relation.EqvGen.trans _ _ _
      (r.sameComponent_directedPostWithBond 3 5 ⟨1,by decide⟩ h3) hpath,hdeg⟩
  · exact ⟨r.vertex 4,hmem 4 (by decide),
      r.sameComponent_directedPostWithBond 3 5 ⟨1,by decide⟩ h4,h4low⟩

end WaveTurbulence.Mole
