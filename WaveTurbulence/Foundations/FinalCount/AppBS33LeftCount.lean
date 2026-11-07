/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33LeftEnergy
import Mathlib.Tactic

/-! # Counting left component labels before choosing the internal pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbS33LeftAdmissibility {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop) (ζ : AppbSideDart
      (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r) → (Fin d → ℤ)) : Prop :=
  ∃ κ,Adm κ ∧ (∀ x,κ (M.mate x) = κ x) ∧ appbS33LeftLabels r κ = ζ

theorem appb_s33_left_spatial {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (p : AppbCountParameters M d) (κ : D → (Fin d → ℤ))
    (hres : M.IsRestricted L γ δ w p.energy p.center κ) :
    ∀ x,‖Molecule.kvec L w (appbS33LeftLabels r κ) x-(appbS33LeftParameters r hg p).center x‖ ≤ 1 := by
  rintro ⟨x,hx⟩
  rcases x with x | t
  · exact hres.2 x.val
  · exact hres.2 (r.edge ⟨1,by decide⟩).val

/-- A single widened energy window costs linearly in the component size.
In particular no power of the number of atoms is lost per atom. -/
theorem appb_s33_left_image_count_le {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} {L γ δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (p : AppbCountParameters M d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (T : Finset (D → (Fin d → ℤ)))
    (hT : ∀ κ ∈ T,κ ∈ p.decorations L γ δ w Adm) :
    ((T.image (appbS33LeftLabels r)).card : ℕ∞) ≤
      (2*((appbS33Side r).card+1)+2)*appbCountE (appbS33LeftMolecule r hg) L γ δ w
        (appbS33LeftAdmissibility r Adm) := by
  classical
  have hs := appb_s33_side_labels_topology M r (appb_s33_splitTopology_of_geometry hg)
  apply appb_one_window_count_le (appbS33LeftMolecule r hg) hL hδ w
    (appbS33LeftParameters r hg p) (appbS33LeftAdmissibility r Adm) (r.vertex 5) hs.2.2.2.2.1
  intro ζ hζ
  obtain ⟨κ,hκ,rfl⟩ := Finset.mem_image.mp hζ
  have hh := hT κ hκ
  refine ⟨appb_s33_left_isDecoration r hg L w p κ hh.1,⟨κ,hh.2.2,hh.1.1,rfl⟩,
    appb_s33_left_spatial r hg L γ δ w p κ hh.2.1,?_⟩
  intro v hv
  have he := appb_s33_side_reinsert_energy_window r hg L γ δ w p κ hh.1 hh.2.1 v hv
  change |(appbSideMolecule (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r) _).Gamma
      L w (appbS33LeftLabels r κ) v-_| ≤ _
  unfold appbS33LeftLabels
  have hvS : v ∈ appbS33Side r := hv
  rw [appb_side_Gamma_eq (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r)
    (appb_s33_reinsert_closedSide M r (appb_s33_splitTopology_of_geometry hg) ⟨1,by decide⟩)
    L w (r.reinsertedLabels κ ⟨1,by decide⟩) hvS]
  simpa only [appbS33LeftParameters,appbSideParameters,Nat.cast_add,Nat.cast_one] using he

end WaveTurbulence.Mole
