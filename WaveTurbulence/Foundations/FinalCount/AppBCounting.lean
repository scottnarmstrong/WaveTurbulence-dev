/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadder
public import WaveTurbulence.Foundations.FinalCount.MoleculeCountingQuantities
import Mathlib.Tactic

/-! # DH23 Appendix B counting conventions

DH23 B.1 expressly permits nonzero c_v at degree-four atoms. This source
variant has a distinct name and does not change the accepted B2 countE.
Selected ladders use the adopted DEGEN source convention. Operation bounds
are inequalities, including at zero post-count (F59).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- B2-CL-7 operation bound, copied with its exact inequality body into the
packet namespace. The ratio is not used to encode operation bounds. -/
def IsDeviation (Apre Apos I : ℝ≥0∞) : Prop := Apre ≤ I * Apos

/-- DH23 B.1 count with unrestricted conservation parameters at every atom. -/
noncomputable def appbCountE (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) : ℕ∞ :=
  ⨆ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (_ : ∀ x, k0 (M.mate x) = k0 x),
    {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}.encard

/-- Actual admissibility restrictions reduce the Appendix B count. -/
theorem appbCountE_mono (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    {Adm Adm' : (D → (Fin d → ℤ)) → Prop} (h : ∀ κ, Adm κ → Adm' κ) :
    appbCountE M L γ δ w Adm ≤ appbCountE M L γ δ w Adm' := by
  unfold appbCountE
  apply iSup_mono
  intro c
  apply iSup_mono
  intro β
  apply iSup_mono
  intro k0
  apply iSup_mono
  intro hk0
  apply Set.encard_mono
  intro κ hκ
  exact ⟨hκ.1,hκ.2.1,h κ hκ.2.2⟩

end WaveTurbulence.Mole
