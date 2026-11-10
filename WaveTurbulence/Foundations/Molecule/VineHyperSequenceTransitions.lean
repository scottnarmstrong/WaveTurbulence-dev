/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperTransitions
public import WaveTurbulence.Foundations.Molecule.VineRungPairIndices
import Mathlib.Tactic

/-! # A hyper-block has at most one transition along any full-rung sequence -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Hyper-block membership is matched on every rung of any length sequence. -/
theorem hyperBlock_sequence_pair_membership (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hH : Mole.IsHyperBlock M S a b) {n : ℕ}
    (Q : FullRungSequence M n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    Q.u i ∈ S ↔ Q.v i ∈ S :=
  hyperBlock_rung_membership M hM hH (Q.upper i hi hin) (Q.lower i hi hin)

end WaveTurbulence.Vine
