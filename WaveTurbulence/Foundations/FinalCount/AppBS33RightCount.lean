/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBConditionedComponentCount
public import WaveTurbulence.Foundations.FinalCount.AppBS33LeftParameters
import Mathlib.Tactic

/-! # Actual right-component count for each fixed internal tuple -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33RightSide {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) : Finset V :=
  (r.directedPostWithBond 3 5 ⟨1,by decide⟩).atoms \ appbS33Side r

noncomputable def appbS33RightMolecule {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r) :=
  appbSideMolecule (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33RightSide r)
    (appb_s33_reinsert_closedSide M r (appb_s33_splitTopology_of_geometry hg) ⟨1,by decide⟩).complement

noncomputable def appbS33RightAdmissibility {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop) :=
  appbSideAdmissibility (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33RightSide r)
    (r.reinsertedPostAdmissibility Adm ⟨1,by decide⟩)

/-- This bound permits the right parameters to depend on the internal
tuple. It does not assert a uniform fixed-parameter global post fiber. -/
theorem appb_s33_right_fiber_card_le {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (p : AppbCountParameters M d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (q : Fin AppbPatternKind.s33.pattern.edges.length → (Fin d → ℤ))
    (ζ : AppbSideDart (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r) → (Fin d → ℤ))
    (T : Finset (D → (Fin d → ℤ)))
    (hT : ∀ κ ∈ T,κ ∈ p.decorations L γ δ w Adm ∧ r.localLabels κ = q ∧ appbS33LeftLabels r κ = ζ) :
    (T.card : ℕ∞) ≤ appbCountE (appbS33RightMolecule r hg) L γ δ w (appbS33RightAdmissibility r Adm) := by
  rw [← Set.encard_coe_eq_coe_finsetCard]
  have hb := appb_conditioned_component_fiber_encard_le M _ r 3 5 (by decide) (by decide)
    (by decide) (by decide) ⟨1,by decide⟩ (appbS33Side r)
    (appb_s33_reinsert_closedSide M r (appb_s33_splitTopology_of_geometry hg) ⟨1,by decide⟩)
    p L γ δ w Adm q ζ
  exact (Set.encard_mono (fun κ hκ => hT κ hκ)).trans hb

end WaveTurbulence.Mole
