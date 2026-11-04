/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.IsCouple
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonCriterion

/-!
# IsCanonC

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defcanon`; T Prop `canonequiv`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- **Canonical layered couples `𝒞_q`** (T Def `defcanon`, last paragraph; criterion form by T Prop
`canonequiv`): `LG ∈ 𝒞_{p+1}` iff `LG` is a couple satisfying `CanonCriterion p` (irreducibility is
automatic for couples). `𝒞₀` is not defined in TARGET; we set it empty (DESIGN Q2). -/
def IsCanonC : ℕ → LayeredGarden 2 → Prop
  | 0, _ => False
  | p + 1, LG => IsCouple LG.garden ∧ LG.CanonCriterion p

end WaveTurbulence
