/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TriplePatterns
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # Source TB selection from an actual triple and the degree-four exclusion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bondsBetween_le_degree (M : Molecule V D) {a b : V} (hab : a ≠ b) :
    M.bondsBetween a b ≤ M.deg a := by
  rw [bondsBetween_eq_card_darts M hab]
  exact Finset.card_filter_le _ _

end WaveTurbulence.Mole.AppbAlgorithm
