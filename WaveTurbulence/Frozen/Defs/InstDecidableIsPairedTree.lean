/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenInstDecidableIsLone
public import WaveTurbulence.Frozen.Defs.GardenIsLone
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf
public import WaveTurbulence.Frozen.Defs.IsPairedTree
public import WaveTurbulence.Frozen.Defs.MarkTag

/-!
# instDecidableIsPairedTree

Wave B tier B1 (WaveB1-Core.lean), source: — (Decidable instance for `IsPairedTree`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

@[instance_reducible, instance] def instDecidableIsPairedTree (G : Garden 1) :
    Decidable (IsPairedTree G) := by
  unfold IsPairedTree
  infer_instance

end WaveTurbulence
