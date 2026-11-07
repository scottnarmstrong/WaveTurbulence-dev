/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinks
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
import Mathlib.Tactic

/-! # Exact compatibility of APPB and G6/G7 normalized counting conventions

Both counts maximize over unrestricted conservation charges and use one
factor for each actual selected length-one ladder. No common gap along a
maximal ladder, positivity, molecule condition, or large-gap premise is
needed for this identity. The shared molecule definitions must be the same
on both sides; this file introduces no alternative molecule carrier.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appbCountE_eq_countEFree (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) :
    appbCountE M L γ δ w Adm = MoleProp.countEFree M L γ δ w Adm := rfl

theorem appbLinks_eq_ladderCells (M : Molecule V D) :
    appbLinks M = MoleProp.ladderCells M := rfl

theorem appbLinkProduct_eq_cellProduct (M : Molecule V D) (L γ δ : ℝ) (P : Finset V → ℝ) :
    appbLinkProduct M L γ δ P = MoleProp.cellProduct M L γ δ P := rfl

/-- Exact equality transfers every APPB count bound to G6/G7 with constant
one, including zero or infinite counts and arbitrary admissibility tests. -/
theorem appbLinkCountA_eq_countAFree (M : Molecule V D) {d : ℕ}
    (L γ δ C1 : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    appbLinkCountA M L γ δ C1 w Adm P = MoleProp.countAFree M L γ δ C1 w Adm P := rfl

/-- Direct transfer without division or a nonzero-count condition. -/
theorem countAFree_le_iff_appbLinkCountA_le (M : Molecule V D) {d : ℕ}
    (L γ δ C1 : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (B : ℝ≥0∞) :
    MoleProp.countAFree M L γ δ C1 w Adm P ≤ B ↔ appbLinkCountA M L γ δ C1 w Adm P ≤ B := Iff.rfl

end WaveTurbulence.Mole.AppbAlgorithm
