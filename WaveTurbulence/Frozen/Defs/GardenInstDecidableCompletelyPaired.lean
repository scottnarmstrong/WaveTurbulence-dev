/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenCompletelyPaired
public import WaveTurbulence.Frozen.Defs.InstDecidableEqGLeaf
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf

/-!
# Garden.instDecidableCompletelyPaired

Wave B tier B1 (WaveB1-Core.lean), source: — (Decidable instance for `CompletelyPaired`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace Garden

variable {w : ℕ} (G : Garden w)

@[instance_reducible, instance] def instDecidableCompletelyPaired (S : Finset (GLeaf G.tree)) :
    Decidable (G.CompletelyPaired S) := by
  unfold CompletelyPaired
  infer_instance

end Garden
end WaveTurbulence
