/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchIsParentOf
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenInstDecidableIsFlower
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstDecidableIsParentOf
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf

/-!
# instDecidableIsFlowerParent

Wave B tier B1 (WaveB1-System.lean), source: — (Decidable instance for `IsFlowerParent`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}

@[instance_reducible, instance] def instDecidableIsFlowerParent (G : Garden w) (b : GBranch G.tree) :
    Decidable (G.IsFlowerParent b) := by
  unfold Garden.IsFlowerParent
  infer_instance

end Kernels
end WaveTurbulence
