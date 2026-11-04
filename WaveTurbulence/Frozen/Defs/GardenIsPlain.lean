/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.MarkTag

/-!
# Garden.IsPlain

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defgarden`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace Garden

variable {w : ℕ} (G : Garden w)

/-- An ordinary garden (T Def `defgarden`): no marked leaves, all leaves paired. -/
def IsPlain : Prop := ∀ ℓ, G.mark ℓ = none

end Garden
end WaveTurbulence
