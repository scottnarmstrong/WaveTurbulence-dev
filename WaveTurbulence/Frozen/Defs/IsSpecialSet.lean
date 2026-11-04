/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.AddrExt
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# IsSpecialSet

Wave B tier B2 (WaveB2-Regular.lean), source: T Def `defencpl`, L1127. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **Special subsets** (T Def `defencpl`, L1127): `Z ⊆ 𝒩^ch` such that for each `𝔫 ∈ Z` the node
linked with `𝔫` is a child of `𝔫`. -/
def IsSpecialSet {w : ℕ} (links : List ((Fin w × Path) × (Fin w × Path)))
    (Z : Finset (Fin w × Path)) : Prop :=
  ∀ z ∈ Z, ∃ i : Fin 3, (z, addrExt z [i]) ∈ links

end WaveTurbulence
