/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionFibers
import Mathlib.Tactic

/-! # Literal large-gap and per-position scale restrictions for DH23 10.1

The unit endpoint has only a lower gap comparison; large gaps are not
truncated physically. Zero scales mean actual zero gap, independently of
large gaps at opposite darts of one atom.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

/-- The source convention |r|∼₀P, with comparability factor 2. -/
def GapScale (L P r : ℝ) : Prop :=
  (P = 0 ∧ r = 0) ∨
  (L⁻¹ ≤ P ∧ P < 1 ∧ P / 2 ≤ r ∧ r ≤ 2 * P) ∨
  (P = 1 ∧ 1 / 2 ≤ r)

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every prescribed molecule constraint, plus actual LG and cell gaps. -/
def CountingAdmissibility (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (w : Mom d)
    (P : Finset V → ℝ) (Extra : (D → (Fin d → ℤ)) → Prop)
    (κ : D → (Fin d → ℤ)) : Prop :=
  LargeGap M L γ η w κ ∧ CellGapRestriction M L w P (GapScale L) κ ∧ Extra κ

/-- The actual projected problem retains LG, every surviving position's
scale and a completion satisfying every old extra constraint. -/
theorem erasedFreeAdmissibility_preserves_constraints (M : Molecule V D)
    {d : ℕ} (L γ η : ℝ) (w : Mom d) (Y : Finset V)
    (P : Finset V → ℝ) (Extra : (D → (Fin d → ℤ)) → Prop)
    {κ' : Degen.RetainedDart M Y → (Fin d → ℤ)}
    (h : erasedFreeAdmissibility M Y (CountingAdmissibility M L γ η w P Extra) κ') :
    CountingAdmissibility (Degen.eraseAtoms M Y) L γ η w P
      (erasedFreeAdmissibility M Y Extra) κ' := by
  obtain ⟨κ,hκ,hb,rfl⟩ := h
  exact ⟨largeGap_erase M L γ η w Y hκ.1,
    cellGapRestriction_erase M L w Y P (GapScale L) hκ.2.1,κ,hκ.2.2,hb,rfl⟩

end WaveTurbulence.MoleProp
