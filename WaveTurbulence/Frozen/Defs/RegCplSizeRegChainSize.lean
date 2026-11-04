/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# RegCpl.size, RegChain.size (mutual)

Wave B tier B2 (WaveB2-Regular.lean): one `mutual` block, frozen as one file because Lean cannot
split it; each declaration keeps its own manifest entry. Sources:
- `RegCpl.size`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850
- `RegChain.size`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850

Frozen by ruling D8 (`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

mutual
/-- The order `n(𝒬)` of the decoded couple (number of branching nodes; characterization
`size_eq_order` in §4). -/
def RegCpl.size : RegCpl → ℕ
  | .triv => 0
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.size + Q₂.size + Q₃.size + 2
  | .type2 Xp Xm Qlp => Xp.size + Xm.size + Qlp.size

/-- The number of branching nodes of a chain with its couples. -/
def RegChain.size : RegChain → ℕ
  | .nil => 0
  | .pair _ Qr Qg inner rest => Qr.size + Qg.size + inner.size + rest.size + 2
end

end WaveTurbulence
