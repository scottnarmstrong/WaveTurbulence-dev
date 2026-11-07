/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ScaleConditions
import Mathlib.Tactic

/-! # Restrictions inherited by actual atom erasure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem projected_largeGap (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (w : Mom d)
    (Y : Finset V) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGap M L γ η w κ) :
    ∀ κ, erasedFreeAdmissibility M Y Adm κ → LargeGap (Degen.eraseAtoms M Y) L γ η w κ := by
  intro κ hκ
  obtain ⟨κ0,h0,_hb,rfl⟩ := hκ
  exact largeGap_erase M L γ η w Y (hAdm κ0 h0)

theorem projected_cellGap (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d)
    (Y : Finset V) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hAdm : ∀ κ, Adm κ → CellGapRestriction M L w P (GapScale L) κ) :
    ∀ κ, erasedFreeAdmissibility M Y Adm κ →
      CellGapRestriction (Degen.eraseAtoms M Y) L w P (GapScale L) κ := by
  intro κ hκ
  obtain ⟨κ0,h0,_hb,rfl⟩ := hκ
  exact cellGapRestriction_erase M L w Y P (GapScale L) (hAdm κ0 h0)

end WaveTurbulence.MoleProp
