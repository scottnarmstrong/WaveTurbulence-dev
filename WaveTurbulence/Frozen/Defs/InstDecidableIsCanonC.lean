/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.InstDecidableIsCouple
public import WaveTurbulence.Frozen.Defs.IsCanonC
public import WaveTurbulence.Frozen.Defs.IsCouple
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonCriterion
public import WaveTurbulence.Frozen.Defs.LayeredGardenInstDecidableCanonCriterion

/-!
# instDecidableIsCanonC

Wave B tier B1 (WaveB1-Core.lean), source: — (Decidable instance for `IsCanonC`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

@[instance_reducible, instance] def instDecidableIsCanonC (q : ℕ) (LG : LayeredGarden 2) :
    Decidable (IsCanonC q LG) :=
  match q with
  | 0 => isFalse fun h => h
  | p + 1 => inferInstanceAs (Decidable (IsCouple LG.garden ∧ LG.CanonCriterion p))

end WaveTurbulence
