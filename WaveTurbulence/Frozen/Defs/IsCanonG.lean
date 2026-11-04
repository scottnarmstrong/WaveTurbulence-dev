/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GardenIrreducible
public import WaveTurbulence.Frozen.Defs.GardenIsPlain
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonCriterion

/-!
# IsCanonG

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defcanon`, L657–L668; T Prop `canonequiv`, L889. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- **Canonical layered gardens `𝒢_q`** (T Def `defcanon`, L657–L668, in the equivalent criterion
form of T Prop `canonequiv`, L889; route R12): `𝒢₀ = ∅`, and `LG ∈ 𝒢_{p+1}` iff the garden is plain,
proper (width `≥ 4`), irreducible and satisfies `CanonCriterion p`. The agreement with the inductive
construction of Def `defcanon` is the B1 anchor `canonicalCharacterization` (B1.11, review G-2). -/
def IsCanonG {w : ℕ} : ℕ → LayeredGarden w → Prop
  | 0, _ => False
  | p + 1, LG => 4 ≤ w ∧ LG.garden.IsPlain ∧ LG.garden.Irreducible ∧ LG.CanonCriterion p

end WaveTurbulence
