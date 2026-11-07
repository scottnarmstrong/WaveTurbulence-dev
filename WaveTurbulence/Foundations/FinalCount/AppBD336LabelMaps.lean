/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD336SecondPair
public import WaveTurbulence.Foundations.FinalCount.AppBLocalLabels
import Mathlib.Tactic

/-! # Exact old coordinates of both successive 3D3New local-label maps -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D K : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_d336_first_local_labels {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33new.pattern) (κ : D → K)
    (j : Fin AppbPatternKind.d33.pattern.edges.length) :
    (appbD336FirstPair r).localLabels κ j = r.localLabels κ (appbD336FirstEmbedding j) := rfl

theorem appb_d336_second_local_labels {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33new.pattern) (κ : D → K)
    (j : Fin appbD336ResidualPattern.edges.length) :
    (appbD336SecondPair r).localLabels ((appbD336FirstPair r).retainedLabels κ) j =
      r.localLabels κ (appbD336SecondEmbedding j) := rfl

end WaveTurbulence.Mole
