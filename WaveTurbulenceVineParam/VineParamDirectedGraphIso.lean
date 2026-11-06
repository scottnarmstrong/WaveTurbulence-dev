/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedBondChart
import Mathlib.Tactic

/-! # Exact directed graph isomorphisms for source-template reindexing -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Every atom and every individually marked bond is transported, with
both directed endpoints preserved. -/
structure DirectedGraphIso {V W β δ : Type*} (ends : β → V×V) (other : δ → W×W) where
  atom : V ≃ W
  edge : β ≃ δ
  endpoints : ∀ e,other (edge e)=(atom (ends e).1,atom (ends e).2)

namespace DirectedGraphIso
variable {V W β δ : Type*} [DecidableEq V] [DecidableEq W]
  [Fintype V] [Fintype W] [Fintype β] [Fintype δ]
  {ends : β → V×V} {other : δ → W×W} (I : DirectedGraphIso ends other)

/-- An exact directed graph isomorphism is an actual full bond model of
the target graph molecule, with no discarded or duplicated occurrences. -/
@[expose] noncomputable def bondModel : DirectedBondModel (graphMolecule other) univ V β where
  ends := ends
  atom := I.atom.trans (DirectedBondModel.graphModel other).atom
  edge := I.edge.trans (graphBondEquiv other)
  tail := by
    intro e
    change (other (I.edge e)).1=I.atom (ends e).1
    rw [I.endpoints]
  head := by
    intro e
    change (other (I.edge e)).2=I.atom (ends e).2
    rw [I.endpoints]

end DirectedGraphIso
end WaveTurbulence.Vine.Param
