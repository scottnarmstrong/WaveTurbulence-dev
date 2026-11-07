/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Terminal
public import WaveTurbulence.Foundations.FinalCount.AppBLinks
import Mathlib.Tactic

/-! # The normalized count at the terminal graph is at most one -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem terminal_countE_le_one (M : Molecule V D) (h : M.bonds = ∅) {d : ℕ}
    (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    appbCountE M L γ δ w Adm ≤ 1 := by
  letI := isEmpty_darts_of_no_bonds M h
  unfold appbCountE
  apply iSup_le
  intro c
  apply iSup_le
  intro β
  apply iSup_le
  intro k0
  apply iSup_le
  intro hk0
  apply Set.encard_le_one_iff_subsingleton.mpr
  intro a ha b hb
  exact Subsingleton.elim _ _

theorem terminal_linkCountA_le_one (M : Molecule V D) (h : M.bonds = ∅) {d : ℕ}
    (L γ δ C1 : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    appbLinkCountA M L γ δ C1 w Adm P ≤ 1 := by
  have hc := ENat.toENNReal_mono (terminal_countE_le_one M h L γ δ w Adm)
  have hp : appbLinkProduct M L γ δ P = 1 := by
    unfold appbLinkProduct
    rw [links_empty_of_no_bonds M h,Finset.prod_empty]
  unfold appbLinkCountA
  rw [circuitRank_zero_of_no_bonds M h,hp]
  simpa using hc

end WaveTurbulence.Mole.AppbAlgorithm
