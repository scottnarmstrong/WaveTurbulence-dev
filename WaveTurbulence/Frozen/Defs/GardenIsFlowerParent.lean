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
public import WaveTurbulence.Frozen.Defs.GardenIsFlower

/-!
# Garden.IsFlowerParent

Wave B tier B1 (WaveB1-System.lean), source: T (kqflower). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}

/-- The parent `𝔣^pr` of a flower: its time is fixed (`δ(t_{𝔣^pr} - s)`, T (kqflower)). -/
def Garden.IsFlowerParent (G : Garden w) (b : GBranch G.tree) : Prop :=
  ∃ ℓ : GLeaf G.tree, G.IsFlower ℓ ∧ b.IsParentOf ℓ

end Kernels
end WaveTurbulence
