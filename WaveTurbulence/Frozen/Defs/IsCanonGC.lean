/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIrreducible
public import WaveTurbulence.Frozen.Defs.GardenIsPlain
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonCriterion

/-!
# IsCanonGC

Wave B tier B1 (WaveB1-System.lean), source: (section) WAVE-B v2 §2.4.3. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- `𝒢_q ∪ 𝒞_q` as one predicate on layered gardens of any width: width `≥ 4`: `IsCanonG`; width
`2`: a couple of `𝒞_q` (probes `isCanonGC_iff_G`, `isCanonGC_iff_C`). -/
def IsCanonGC {w : ℕ} : ℕ → LayeredGarden w → Prop
  | 0, _ => False
  | p + 1, LG => LG.garden.IsPlain ∧
      ((4 ≤ w ∧ LG.garden.Irreducible) ∨ (w = 2 ∧ ∀ j, LG.garden.sig j = (-1) ^ (j : ℕ))) ∧
      LG.CanonCriterion p

end WaveTurbulence
