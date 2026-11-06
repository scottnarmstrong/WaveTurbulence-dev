/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamPhysicalChartSupport
import Mathlib.Tactic

/-! # Geometric side support on the enlarged actual atom set -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V]

/-- An old cap retains its exact old atoms and excludes both fresh vertices. -/
@[expose] def liftedCap (C : Finset V) : Finset (V ⊕ Fin 2) := C.image Sum.inl

/-- A physical bond touches the designated side of a cap. -/
@[expose] def touchesSide (ends : β → V×V) (C : Finset V) (e : β) (side : Bool) : Prop :=
  if side then (ends e).1 ∈ C ∨ (ends e).2 ∈ C
    else (ends e).1 ∉ C ∨ (ends e).2 ∉ C

/-- Common-side support is exactly a geometric Boolean side for each fixed
pair of physical origins. -/
theorem physicalCapSupported_iff [Fintype V] [Fintype β]
    {ends : β → V×V} {X : VineType} {a b : V}
    (P : PhysicalGraphChart ends X a b) (C : Finset V) :
    P.CapSupported C ↔ ∀ i,∃ side : Bool,
      touchesSide ends C (P.differencePair i).1 side ∧
        touchesSide ends C (P.differencePair i).2 side := by
  constructor
  · intro h i
    rcases h i with h | h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  · intro h i
    obtain ⟨side,hs⟩ := h i
    cases side
    · exact Or.inr hs
    · exact Or.inl hs

end WaveTurbulence.Vine.Param
