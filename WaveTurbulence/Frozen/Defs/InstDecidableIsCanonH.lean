/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenInstDecidableIsFlowerGarden
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerGarden
public import WaveTurbulence.Frozen.Defs.InstFintypeGNode
public import WaveTurbulence.Frozen.Defs.IsCanonH
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonCriterion
public import WaveTurbulence.Frozen.Defs.LayeredGardenInstDecidableCanonCriterion
public import WaveTurbulence.Frozen.Defs.LayeredGardenInstDecidableOnStem
public import WaveTurbulence.Frozen.Defs.LayeredGardenOnStem

/-!
# instDecidableIsCanonH

Wave B tier B1 (WaveB1-Core.lean), source: — (Decidable instance for `IsCanonH`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

@[instance_reducible, instance] def instDecidableIsCanonH {w : ℕ} (q : ℕ) (LG : LayeredGarden w) :
    Decidable (IsCanonH q LG) :=
  match q with
  | 0 => isFalse fun h => h
  | p + 1 => inferInstanceAs (Decidable (LG.garden.IsFlowerGarden ∧
      (∀ a, LG.OnStem a → LG.layer a = p) ∧ LG.CanonCriterion p))

end WaveTurbulence
