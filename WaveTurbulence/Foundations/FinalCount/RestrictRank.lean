/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RestrictLad
/-! Restriction, part 4 (FINALCOUNT-G2 infrastructure): the circuit rank and the ladder weight are additive. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) (P : V → Prop) [DecidablePred P] (h : PClosed M P)

theorem circuitRank_restrictP_add :
    (restrictP M P h).circuitRank + (restrictP M (fun a => ¬ P a) h.neg).circuitRank = M.circuitRank := by
  unfold Molecule.circuitRank
  have h1 := restrictP_bonds_card M P h
  have h2 := restrictP_atoms_card M P h
  have h3 := numComponents_restrictP_add M P h
  push_cast
  have h1' : (((restrictP M P h).bonds.card : ℤ) + ((restrictP M (fun a => ¬ P a) h.neg).bonds.card : ℤ)) = M.bonds.card := by
    exact_mod_cast h1
  have h2' : (((restrictP M P h).atoms.card : ℤ) + ((restrictP M (fun a => ¬ P a) h.neg).atoms.card : ℤ)) = M.atoms.card := by
    exact_mod_cast h2
  have h3' : (((restrictP M P h).numComponents : ℤ) + ((restrictP M (fun a => ¬ P a) h.neg).numComponents : ℤ)) = M.numComponents := by
    exact_mod_cast h3
  linarith

/-- The ladder product of `M` is the product over the two halves. -/
theorem ladderProd_restrictP (f : Finset V → ℝ) :
    ∏ S ∈ M.maximalLadders, f S =
      (∏ S ∈ (restrictP M P h).maximalLadders, f S) *
        ∏ S ∈ (restrictP M (fun a => ¬ P a) h.neg).maximalLadders, f S := by
  rw [maximalLadders_restrict_union M P h, Finset.prod_union (maximalLadders_restrict_disjoint M P h)]

end WaveTurbulence.FinalCount
