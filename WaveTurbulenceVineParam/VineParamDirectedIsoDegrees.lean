/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedGraphIso
import Mathlib.Tactic

/-! # Actual balanced source degrees transport through directed occurrence isomorphisms -/

public section
namespace WaveTurbulence.Vine.Param.DirectedGraphIso
open Finset
variable {V W β δ : Type*} [DecidableEq V] [DecidableEq W]
  [Fintype β] [Fintype δ]
  {ends : β → V×V} {other : δ → W×W} (I : DirectedGraphIso ends other)

/-- Complete outgoing-minus-incoming degree is invariant under the exact
atom and individual-bond reindexing. -/
theorem degree_eq (v : V) :
    (∑ e,-energySign other (I.atom v) e)=∑ e,-energySign ends v e := by
  have hi : ∀ u w,I.atom u=I.atom w ↔ u=w := fun _ _ =>
    ⟨fun h => I.atom.injective h,fun h => congrArg I.atom h⟩
  calc
    _=(∑ e : β,-energySign other (I.atom v) (I.edge e)) :=
      (I.edge.sum_comp (fun e => -energySign other (I.atom v) e)).symm
    _=_ := by
      apply sum_congr rfl
      intro e _
      simp only [energySign,I.endpoints,hi]

end WaveTurbulence.Vine.Param.DirectedGraphIso
