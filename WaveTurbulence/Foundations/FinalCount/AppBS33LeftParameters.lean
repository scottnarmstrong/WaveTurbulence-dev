/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33SideReinsertEnergy
public import WaveTurbulence.Foundations.FinalCount.AppBGlueParameters
import Mathlib.Tactic

/-! # Fixed parameters for the actual left component in 3S3 reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33SideFullParameters {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ} (p : AppbCountParameters M d) :
    AppbCountParameters (r.directedPostWithBond 3 5 ⟨1,by decide⟩) d where
  momentum := appbS33SideReinsertMomentum r p.momentum
  energy := appbS33SideReinsertEnergy r p.energy
  center := Sum.elim (fun x => p.center x.val) (fun _ => p.center (r.edge ⟨1,by decide⟩).val)
  center_mate := by
    unfold AppbRealization.directedPostWithBond
    split_ifs
    all_goals rintro (x|t)
    · exact p.center_mate x.val
    · rfl
    · exact p.center_mate x.val
    · rfl

noncomputable def appbS33LeftMolecule {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r) :=
  appbSideMolecule (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r)
    (appb_s33_reinsert_closedSide M r (appb_s33_splitTopology_of_geometry hg) ⟨1,by decide⟩)

noncomputable def appbS33LeftParameters {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (p : AppbCountParameters M d) : AppbCountParameters (appbS33LeftMolecule r hg) d :=
  appbSideParameters (appbS33Side r)
    (appb_s33_reinsert_closedSide M r (appb_s33_splitTopology_of_geometry hg) ⟨1,by decide⟩)
    (appbS33SideFullParameters r p)

noncomputable def appbS33LeftLabels {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ} (κ : D → (Fin d → ℤ)) :=
  appbSideLabels (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r)
    (r.reinsertedLabels κ ⟨1,by decide⟩)

/-- The conservation sources on the left component are fixed before the
internal pair is chosen. Only the old source parameters enter them. -/
theorem appb_s33_left_isDecoration {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (L : ℝ) (w : Mom d) (p : AppbCountParameters M d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w p.momentum κ) :
    (appbS33LeftMolecule r hg).IsDecoration L w (appbS33LeftParameters r hg p).momentum
      (appbS33LeftLabels r κ) := by
  have h3 := r.vertex_mem_post 3 (by decide) (by decide)
  have h5 := r.vertex_mem_post 5 (by decide) (by decide)
  have hr := Degen.isDecoration_eraseAtoms M r.removedAtoms hκ
  have hm : (r.directedPostWithBond 3 5 ⟨1,by decide⟩).IsDecoration L w
      (appbS33SideDirectedMomentum r L w p.momentum κ) (r.reinsertedLabels κ ⟨1,by decide⟩) := by
    unfold AppbRealization.directedPostWithBond appbS33SideDirectedMomentum
    split_ifs
    · exact appb_isDecoration_addBond r.post (r.vertex 3) (r.vertex 5) h3 h5
        (κ (r.edge ⟨1,by decide⟩).val) hr
    · exact appb_isDecoration_addBond r.post (r.vertex 5) (r.vertex 3) h5 h3
        (κ (r.edge ⟨1,by decide⟩).val) hr
  have hh := appb_isDecoration_side (appbS33Side r)
    (appb_s33_reinsert_closedSide M r (appb_s33_splitTopology_of_geometry hg) ⟨1,by decide⟩) L w _ _ hm
  refine ⟨hh.1,?_⟩
  intro v hv
  exact (hh.2 v hv).trans (appb_s33_side_directed_momentum_eq r hg L w p.momentum κ hκ hv)

end WaveTurbulence.Mole
