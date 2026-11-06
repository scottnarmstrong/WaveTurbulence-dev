/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamContractCoordinates
public import WaveTurbulence.Foundations.Molecule.VineTemplates
import Mathlib.Tactic

/-! # Exact base template shapes in the full-vine contract, including F72 -/

public section
namespace WaveTurbulence.Vine.Param
open VineParamContract

/-- The number of paired phase slots of each pinned base template.
VII includes its distinguished single-bond junction pair. -/
@[expose] def basePairCount : VineType → ℕ
  | .I => 0
  | .II => 1
  | .III | .IV | .V => 2
  | .VI => 5
  | .VII | .VIII => 3

/-- The pinned type-II base is exactly the m=1 Q-block. -/
@[expose] def normalizedBaseShape (X : VineType) : Shape X where
  m := basePairCount X
  typeI := by intro h; subst X; rfl
  typeII := by intro h; subst X; decide

/-- The source base template has exactly one more atom than its included
contract indexing. No even/odd endpoint is suppressed. -/
theorem normalizedBaseShape_atoms (X : VineType) : (normalizedBaseShape X).n+1=X.template.n := by
  cases X <;> decide

/-- The base source has exactly twice as many bonds as free coordinates. -/
theorem normalizedBaseShape_bonds (X : VineType) :
    X.template.bonds.length=2*(normalizedBaseShape X).n := by
  cases X <;> decide

/-- Every base chart has a nonempty physical reference block. -/
theorem normalizedBaseShape_pos (X : VineType) : 0<(normalizedBaseShape X).n := by
  cases X <;> decide

end WaveTurbulence.Vine.Param
