/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDirectedReinsertGap
public import WaveTurbulence.Foundations.FinalCount.AppBEndpointSigns
public import WaveTurbulence.Foundations.FinalCount.AppBS33ReinsertSigns
import Mathlib.Tactic

/-! # DH23 3S3-3G and 3D3-3G preserve the source LG threshold additively -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_reinsert_largeGap {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitGeometry M r)
    {d : ℕ} {L γ γ0 g : ℝ} (w : Mom d) (κ : D → (Fin d → ℤ))
    (hm : ∀ x,κ (M.mate x) = κ x) (hLG : AppbLargeGap M L w κ g)
    (hlabel : AppbS33LabelConditions M r L γ γ0 w κ) (hL : 0 ≤ L) :
    AppbLargeGap (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L w
      (r.reinsertedLabels κ ⟨1,by decide⟩) (g-L^(-γ)) := by
  have hOpp : AppbOppositeFrom M (r.vertex 3) (r.vertex 5)
      (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val :=
    (appb_incidence_sign_opposite_from M _ _ _ _).mp (appb_s33_external_signs_opposite r hgeom.2.2.2.1)
  apply appb_directed_reinsert_largeGap M r.removedAtoms (r.vertex 3) (r.vertex 5) (r.vertex 1) (r.vertex 2)
    (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 5 (by decide) (by decide))
    (mem_image_of_mem _ (by decide)) (mem_image_of_mem _ (by decide))
    (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val
    ((r.endpoints ⟨1,by decide⟩).trans Sym2.eq_swap) ((r.endpoints ⟨3,by decide⟩).trans Sym2.eq_swap)
    (mem_filter.mp (mem_filter.mp (r.edge ⟨1,by decide⟩).property).1).2
    (mem_filter.mp (mem_filter.mp (r.edge ⟨3,by decide⟩).property).1).2
    hOpp L w κ hm g (L^(-γ)) (Real.rpow_nonneg hL _) hLG
  have hn := norm_nonneg (Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
    Molecule.kvec L w κ (r.edge ⟨4,by decide⟩).val)
  linarith only [hlabel.1,hn]

theorem appb_d33_reinsert_largeGap {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (hOpp : AppbD33BoundaryOpposite M r)
    {d : ℕ} {L γ γ0 g : ℝ} (w : Mom d) (κ : D → (Fin d → ℤ))
    (hm : ∀ x,κ (M.mate x) = κ x) (hLG : AppbLargeGap M L w κ g)
    (hlabel : AppbD33LabelConditions M r L γ γ0 w κ) (hL : 0 ≤ L) :
    AppbLargeGap (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L w
      (r.reinsertedLabels κ ⟨2,by decide⟩) (g-L^(-γ)) := by
  have ho : AppbOppositeFrom M (r.vertex 3) (r.vertex 4)
      (r.edge ⟨2,by decide⟩).val (r.edge ⟨3,by decide⟩).val :=
    (appb_incidence_sign_opposite_from M _ _ _ _).mp (appb_d33_external_signs_opposite r hOpp)
  exact appb_directed_reinsert_largeGap M r.removedAtoms (r.vertex 3) (r.vertex 4) (r.vertex 1) (r.vertex 2)
    (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 4 (by decide) (by decide))
    (mem_image_of_mem _ (by decide)) (mem_image_of_mem _ (by decide))
    (r.edge ⟨2,by decide⟩).val (r.edge ⟨3,by decide⟩).val
    ((r.endpoints ⟨2,by decide⟩).trans Sym2.eq_swap) ((r.endpoints ⟨3,by decide⟩).trans Sym2.eq_swap)
    (mem_filter.mp (mem_filter.mp (r.edge ⟨2,by decide⟩).property).1).2
    (mem_filter.mp (mem_filter.mp (r.edge ⟨3,by decide⟩).property).1).2
    ho L w κ hm g (L^(-γ)) (Real.rpow_nonneg hL _) hLG hlabel.1

end WaveTurbulence.Mole
