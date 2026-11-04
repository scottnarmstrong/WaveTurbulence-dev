/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.AddrExt
public import WaveTurbulence.Frozen.Defs.IsSpecialSet
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# instDecidableIsSpecialSet

Wave B tier B2 (WaveB2-Regular.lean), source: — (Decidable instance for `IsSpecialSet`; no source object). Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

@[instance_reducible, instance] def instDecidableIsSpecialSet {w : ℕ} (links : List ((Fin w × Path) × (Fin w × Path)))
    (Z : Finset (Fin w × Path)) : Decidable (IsSpecialSet links Z) := by
  unfold IsSpecialSet
  infer_instance

end WaveTurbulence
