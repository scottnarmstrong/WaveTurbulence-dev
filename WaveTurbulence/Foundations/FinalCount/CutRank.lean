/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutComp3
/-! Circuit rank of a cut (FINALCOUNT-G2 step 1): `χ_cut = χ - 1` for an α-cut, `χ_cut = χ` for a β-cut. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem cut_bonds : (M.cut v v₂ x₁ x₂).bonds = M.bonds := rfl

theorem cut_atoms_card (hcd : M.IsCutData v v₂ x₁ x₂) :
    (M.cut v v₂ x₁ x₂).atoms.card = M.atoms.card + 1 :=
  Finset.card_insert_of_notMem hcd.2.1

theorem circuitRank_cut_eq (hcd : M.IsCutData v v₂ x₁ x₂) :
    (M.cut v v₂ x₁ x₂).circuitRank = M.circuitRank - 1 +
      (((M.cut v v₂ x₁ x₂).numComponents : ℤ) - M.numComponents) := by
  unfold Molecule.circuitRank
  rw [cut_bonds, cut_atoms_card M hcd]
  push_cast; ring

/-- An α-cut keeps the two halves connected. -/
theorem isAlphaCut_iff (hcd : M.IsCutData v v₂ x₁ x₂) :
    M.IsAlphaCut v v₂ x₁ x₂ ↔ (M.cut v v₂ x₁ x₂).SameComponent v v₂ := by
  unfold Molecule.IsAlphaCut
  constructor
  · intro h
    by_contra hn
    have := numComponents_cut_of_not_same M hcd hn
    omega
  · intro h
    rw [numComponents_cut_of_same M hcd h]

theorem circuitRank_cut_alpha (hcd : M.IsCutData v v₂ x₁ x₂) (h : M.IsAlphaCut v v₂ x₁ x₂) :
    (M.cut v v₂ x₁ x₂).circuitRank = M.circuitRank - 1 := by
  rw [circuitRank_cut_eq M hcd, numComponents_cut_of_same M hcd ((isAlphaCut_iff M hcd).1 h)]
  ring

theorem circuitRank_cut_beta (hcd : M.IsCutData v v₂ x₁ x₂) (h : ¬ M.IsAlphaCut v v₂ x₁ x₂) :
    (M.cut v v₂ x₁ x₂).circuitRank = M.circuitRank := by
  rw [circuitRank_cut_eq M hcd,
    numComponents_cut_of_not_same M hcd (fun hs => h ((isAlphaCut_iff M hcd).2 hs))]
  push_cast; ring

end WaveTurbulence.FinalCount
