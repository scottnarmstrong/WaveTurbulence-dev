/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstFintypeGNode
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenParentLayer

/-!
# LayeredGarden.attachNodes

Wave B tier B1 (WaveB1-Core.lean), source: T Prop `canonequiv`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The nodes `𝒰` at which the gardens of `𝒢_p` are attached in the construction of a garden of
`𝒢_{p+1}` (T Prop `canonequiv`, proof): `𝔏_𝔫 < p` and `𝔏_{𝔫^pr} = p` (roots: parent layer `p`). -/
def attachNodes (p : ℕ) : Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun a => LG.layer a < p ∧ LG.parentLayer p a = p

end LayeredGarden
end WaveTurbulence
