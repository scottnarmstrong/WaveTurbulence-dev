/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.InstDecidableEqMarkTag
public import WaveTurbulence.Frozen.Defs.MarkTag

/-!
# instFintypeMarkTag

Wave B tier B1 (WaveB1-Core.lean), source: — (Fintype instance for `MarkTag`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

@[instance_reducible, instance] def instFintypeMarkTag : Fintype MarkTag :=
  ⟨{MarkTag.lower, MarkTag.equal}, fun x => by cases x <;> simp⟩

end WaveTurbulence
