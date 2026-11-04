/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.RegChainIsNil
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# RegCpl.dominant, RegChain.dominant (mutual)

Wave B tier B2 (WaveB2-Regular.lean): one `mutual` block, frozen as one file because Lean cannot
split it; each declaration keeps its own manifest entry. Sources:
- `RegCpl.dominant`: T Prop `propstructure`, L859–L860; DH21 Def 4.17
- `RegChain.dominant`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850

Frozen by ruling D8 (`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

mutual
/-- **Dominant couple codes** (T Prop `propstructure`, L859–L860; DH21 Def 4.17): trivial; type 1 with
dominant `Q_j`; type 2 with dominant chains (`𝒫^ε = {{1,2},…}`) and dominant couples. -/
def RegCpl.dominant : RegCpl → Bool
  | .triv => true
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.dominant && Q₂.dominant && Q₃.dominant
  | .type2 Xp Xm Qlp => Xp.dominant && Xm.dominant && Qlp.dominant

/-- Dominant chains: consecutive pairs `{2j-1, 2j}` (`inner = nil`) with dominant couples. A regular
tree is dominant iff its chain code is. -/
def RegChain.dominant : RegChain → Bool
  | .nil => true
  | .pair _ Qr Qg inner rest => inner.isNil && Qr.dominant && Qg.dominant && rest.dominant
end

end WaveTurbulence
