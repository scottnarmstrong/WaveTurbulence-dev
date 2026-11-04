/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf
public import WaveTurbulence.Frozen.Defs.MarkTag
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# Garden.IsFlowerGarden

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defflower`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace Garden

variable {w : ℕ} (G : Garden w)

/-- A **flower garden** (T Def `defflower`): every tree has exactly one marked leaf, it is a flower,
and the root signs alternate `(+,-,…,+,-)`. TARGET's flower gardens have even width `2P`; the
predicate allows any `w`, and the width is fixed by the consumer (`w := 2 * Pm`; stage-1 O1). -/
def IsFlowerGarden : Prop :=
  (∀ j : Fin w, (Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.mark ℓ ≠ none).card = 1)
    ∧ (∀ ℓ, G.mark ℓ ≠ none → G.IsFlower ℓ) ∧ ∀ j : Fin w, G.sig j = (-1) ^ (j : ℕ)

end Garden
end WaveTurbulence
