/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenInstDecidableIsFlower
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerGarden
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf
public import WaveTurbulence.Frozen.Defs.MarkTag
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# Garden.instDecidableIsFlowerGarden

Wave B tier B1 (WaveB1-Core.lean), source: — (Decidable instance for `IsFlowerGarden`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace Garden

variable {w : ℕ} (G : Garden w)

@[instance_reducible, instance] def instDecidableIsFlowerGarden : Decidable G.IsFlowerGarden := by
  unfold IsFlowerGarden
  infer_instance

end Garden
end WaveTurbulence
