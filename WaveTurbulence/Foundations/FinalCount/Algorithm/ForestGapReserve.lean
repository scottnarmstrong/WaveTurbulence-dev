/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestBondBudget
public import WaveTurbulence.Foundations.FinalCount.AppBIteratedLargeGap
import Mathlib.Tactic

/-! # A bond-budget reserve pays every actual reinsertion gap loss

Each graph edit removes at least one bond. Charging one L^(-γ) per bond
removed therefore covers every reinsertion and is harmless for literal
cuts. Component splitting leaves the bond sum unchanged.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Filter
universe u v
variable {V : Type v} [DecidableEq V]

noncomputable def forestGapReserve (B : ℕ) (L γ η : ℝ) (F : List (State.{u,v} V)) : ℝ :=
  L^(-γ+η)-((B : ℝ)-(forestBonds F : ℝ))*L^(-γ)

end WaveTurbulence.Mole.AppbAlgorithm
