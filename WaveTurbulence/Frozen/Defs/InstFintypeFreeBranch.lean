/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenFreeBranch
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstDecidableIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch

/-!
# instFintypeFreeBranch

Wave B tier B1 (WaveB1-System.lean), source: — (Fintype instance for `FreeBranch`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}

@[instance_reducible, instance] noncomputable def instFintypeFreeBranch (G : Garden w) :
    Fintype G.FreeBranch := by
  unfold Garden.FreeBranch
  infer_instance

end Kernels
end WaveTurbulence
