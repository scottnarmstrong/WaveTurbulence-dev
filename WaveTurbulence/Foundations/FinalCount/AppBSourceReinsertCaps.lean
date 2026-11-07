/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDirectedReinsertCaps
public import WaveTurbulence.Foundations.FinalCount.AppBEndpointSigns
public import WaveTurbulence.Foundations.FinalCount.AppBS33ReinsertSigns
import Mathlib.Tactic

/-! # DH23 3S3-3G and 3D3-3G preserve the source LG threshold additively -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_reinsert_degree_caps {M : Molecule V D} (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitGeometry M r)
    : ∀ v ∈ (r.directedPostWithBond 3 5 ⟨1,by decide⟩).atoms,
      (((r.directedPostWithBond 3 5 ⟨1,by decide⟩).dartsAt v).filter (fun x => (r.directedPostWithBond 3 5 ⟨1,by decide⟩).out x = true)).card ≤ 2 ∧
      (((r.directedPostWithBond 3 5 ⟨1,by decide⟩).dartsAt v).filter (fun x => (r.directedPostWithBond 3 5 ⟨1,by decide⟩).out x = false)).card ≤ 2 := by
  have hOpp : AppbOppositeFrom M (r.vertex 3) (r.vertex 5)
      (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val :=
    (appb_incidence_sign_opposite_from M _ _ _ _).mp (appb_s33_external_signs_opposite r hgeom.2.2.2.1)
  apply appb_directed_reinsert_degree_caps M hM r.removedAtoms (r.vertex 3) (r.vertex 5) (r.vertex 1) (r.vertex 2)
    (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 5 (by decide) (by decide))
    (mem_image_of_mem _ (by decide)) (mem_image_of_mem _ (by decide))
    (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val
    ((r.endpoints ⟨1,by decide⟩).trans Sym2.eq_swap) ((r.endpoints ⟨3,by decide⟩).trans Sym2.eq_swap)
    (mem_filter.mp (mem_filter.mp (r.edge ⟨1,by decide⟩).property).1).2
    (mem_filter.mp (mem_filter.mp (r.edge ⟨3,by decide⟩).property).1).2
    hOpp

theorem appb_d33_reinsert_degree_caps {M : Molecule V D} (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern) (hOpp : AppbD33BoundaryOpposite M r)
    : ∀ v ∈ (r.directedPostWithBond 3 4 ⟨2,by decide⟩).atoms,
      (((r.directedPostWithBond 3 4 ⟨2,by decide⟩).dartsAt v).filter (fun x => (r.directedPostWithBond 3 4 ⟨2,by decide⟩).out x = true)).card ≤ 2 ∧
      (((r.directedPostWithBond 3 4 ⟨2,by decide⟩).dartsAt v).filter (fun x => (r.directedPostWithBond 3 4 ⟨2,by decide⟩).out x = false)).card ≤ 2 := by
  have ho : AppbOppositeFrom M (r.vertex 3) (r.vertex 4)
      (r.edge ⟨2,by decide⟩).val (r.edge ⟨3,by decide⟩).val :=
    (appb_incidence_sign_opposite_from M _ _ _ _).mp (appb_d33_external_signs_opposite r hOpp)
  exact appb_directed_reinsert_degree_caps M hM r.removedAtoms (r.vertex 3) (r.vertex 4) (r.vertex 1) (r.vertex 2)
    (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 4 (by decide) (by decide))
    (mem_image_of_mem _ (by decide)) (mem_image_of_mem _ (by decide))
    (r.edge ⟨2,by decide⟩).val (r.edge ⟨3,by decide⟩).val
    ((r.endpoints ⟨2,by decide⟩).trans Sym2.eq_swap) ((r.endpoints ⟨3,by decide⟩).trans Sym2.eq_swap)
    (mem_filter.mp (mem_filter.mp (r.edge ⟨2,by decide⟩).property).1).2
    (mem_filter.mp (mem_filter.mp (r.edge ⟨3,by decide⟩).property).1).2
    ho

end WaveTurbulence.Mole
