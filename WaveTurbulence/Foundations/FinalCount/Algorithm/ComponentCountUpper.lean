/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBComponentAdmissibility
public import WaveTurbulence.Foundations.FinalCount.AppBComponentRestriction
public import WaveTurbulence.Foundations.FinalCount.AppBSideEquations
import Mathlib.Tactic

/-! # Restriction to closed components gives the matching upper count bound -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem component_countE_upper (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) :
    appbCountE M L γ δ w A ≤
      appbCountE (appbSideMolecule M S hS) L γ δ w (appbSideAdmissibility M S A)*
        appbCountE (appbSideMolecule M (M.atoms \ S) hS.complement) L γ δ w
          (appbSideAdmissibility M (M.atoms \ S) A) := by
  classical
  rw [appbCountE_eq_iSup]
  apply iSup_le
  intro p
  let p1 := appbSideParameters S hS p
  let p2 := appbSideParameters (M.atoms \ S) hS.complement p
  let A1 := appbSideAdmissibility M S A
  let A2 := appbSideAdmissibility M (M.atoms \ S) A
  let f := fun κ : D → (Fin d → ℤ) =>
    (appbSideLabels M S κ,appbSideLabels M (M.atoms \ S) κ)
  have hm : Set.MapsTo f (p.decorations L γ δ w A)
      ((p1.decorations L γ δ w A1) ×ˢ (p2.decorations L γ δ w A2)) := by
    intro κ hκ
    exact ⟨⟨appb_isDecoration_side S hS L w p.momentum κ hκ.1,
      appb_isRestricted_side S hS L γ δ w p.energy p.center κ hκ.2.1,⟨κ,hκ.2.2,rfl⟩⟩,
      ⟨appb_isDecoration_side (M.atoms \ S) hS.complement L w p.momentum κ hκ.1,
      appb_isRestricted_side (M.atoms \ S) hS.complement L γ δ w p.energy p.center κ hκ.2.1,
      ⟨κ,hκ.2.2,rfl⟩⟩⟩
  have hc := Set.encard_le_encard_of_injOn hm (appbSideLabelsPair_injective M S).injOn
  rw [Set.encard_prod] at hc
  have h1 : (p1.decorations L γ δ w A1).encard ≤ appbCountE (appbSideMolecule M S hS) L γ δ w A1 := by
    rw [appbCountE_eq_iSup]
    exact le_iSup (fun p => (p.decorations L γ δ w A1).encard) p1
  have h2 : (p2.decorations L γ δ w A2).encard ≤ appbCountE
      (appbSideMolecule M (M.atoms \ S) hS.complement) L γ δ w A2 := by
    rw [appbCountE_eq_iSup]
    exact le_iSup (fun p => (p.decorations L γ δ w A2).encard) p2
  exact hc.trans (mul_le_mul h1 h2 (by exact bot_le) (by exact bot_le))

end WaveTurbulence.Mole.AppbAlgorithm
