/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GLeafToNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenSign
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf
public import WaveTurbulence.Frozen.Defs.MarkTag

/-!
# inputLeaves

Wave B tier B1 (WaveB1-System.lean), source: T (defkg0). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- The leaves carrying an input factor: sign `+`, not marked (T (defkg0); L682; (kqflower)). -/
def inputLeaves (G : Garden w) : Finset (GLeaf G.tree) :=
  Finset.univ.filter fun ℓ => G.sign ℓ.toNode = 1 ∧ G.mark ℓ = none

end Kernels
end WaveTurbulence
