/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalGeometryStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.FineGeometryStep
import Mathlib.Tactic

/-! # Actual normal/fine traces cannot terminate with negative initial nu

This is an internal run endpoint, not Prop 10.2: the source scheduler must
construct its full run and identify its good-free specialization. All
step increments used below are proved from the actual graph constructors.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

inductive NormalFineStep : State.{u,v} V → State.{u,v} V → Prop
  | normal {s t : State.{u,v} V} {n : ℕ} : NormalGeometryStep s t n → NormalFineStep s t
  | fine {s t : State.{u,v} V} : FineGeometryStep s t → NormalFineStep s t

theorem NormalFineStep.defect_mono {s t : State.{u,v} V} (h : NormalFineStep s t)
    (hM : s.graph.IsMolecule) : defectPotential s.graph ≤ defectPotential t.graph := by
  cases h with
  | normal h => exact h.defect_mono
  | fine h => exact h.defect_mono hM

end WaveTurbulence.Mole.AppbAlgorithm
