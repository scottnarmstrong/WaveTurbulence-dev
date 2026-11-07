/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSourceReinsertCaps
public import WaveTurbulence.Foundations.FinalCount.AppBD33ReinsertDegrees
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertAtoms
import Mathlib.Tactic

/-! # DH23 3D3-3G preserves both molecule axioms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_d33_reinsert_isMolecule (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v)
    (hb : ∀ e : D,¬Degen.IsBridge M e) (ho : AppbD33BoundaryOpposite M r)
    (hdefect : AppbD33ResidualDefect M r) :
    (r.directedPostWithBond 3 4 ⟨2,by decide⟩).IsMolecule := by
  let N := r.directedPostWithBond 3 4 ⟨2,by decide⟩
  have hatoms : N.atoms = M.atoms \ r.removedAtoms :=
    r.directedPostWithBond_atoms 3 4 ⟨2,by decide⟩ (by decide) (by decide) (by decide) (by decide)
  refine ⟨appb_d33_reinsert_degree_caps hM r ho,?_⟩
  obtain ⟨w,hw,hw1,hw2,hd⟩ := hdefect
  have hwY : w ∉ r.removedAtoms := by
    intro h
    obtain ⟨a,ha,he⟩ := mem_image.mp h
    have ha' : a = 1 ∨ a = 2 := by simpa [AppbPatternKind.pattern] using ha
    rcases ha' with rfl | rfl
    · exact hw1 he.symm
    · exact hw2 he.symm
  have hwN : w ∈ N.atoms := hatoms.symm ▸ mem_sdiff.mpr ⟨hw,hwY⟩
  have hf : N.numComponents = 1 := by
    have he := (appb_d33_good_reinsert_graph_effect M r hc hb).1
    have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hc
    exact he.trans hm
  intro v hv
  refine ⟨w,hwN,appb_connected_of_numComponents_eq_one N hf hv hwN,?_⟩
  exact (appb_d33_reinsert_degree M r hwY).trans_ne hd

end WaveTurbulence.Mole
