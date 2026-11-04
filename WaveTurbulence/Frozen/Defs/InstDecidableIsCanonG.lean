/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GardenInstDecidableIrreducible
public import WaveTurbulence.Frozen.Defs.GardenInstDecidableIsPlain
public import WaveTurbulence.Frozen.Defs.GardenIrreducible
public import WaveTurbulence.Frozen.Defs.GardenIsPlain
public import WaveTurbulence.Frozen.Defs.IsCanonG
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonCriterion
public import WaveTurbulence.Frozen.Defs.LayeredGardenInstDecidableCanonCriterion

/-!
# instDecidableIsCanonG

Wave B tier B1 (WaveB1-Core.lean), source: — (Decidable instance for `IsCanonG`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

@[instance_reducible, instance] def instDecidableIsCanonG {w : ℕ} (q : ℕ) (LG : LayeredGarden w) :
    Decidable (IsCanonG q LG) :=
  match q with
  | 0 => isFalse fun h => h
  | p + 1 => inferInstanceAs
    (Decidable (4 ≤ w ∧ LG.garden.IsPlain ∧ LG.garden.Irreducible ∧ LG.CanonCriterion p))

end WaveTurbulence
