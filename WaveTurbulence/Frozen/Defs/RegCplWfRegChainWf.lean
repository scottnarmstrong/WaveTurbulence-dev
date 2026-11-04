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
public import WaveTurbulence.Frozen.Defs.RegCplIsType2
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# RegCpl.wf, RegChain.wf (mutual)

Wave B tier B2 (WaveB2-Regular.lean): one `mutual` block, frozen as one file because Lean cannot
split it; each declaration keeps its own manifest entry. Sources:
- `RegCpl.wf`: T Prop `propstructure`
- `RegChain.wf`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850

Frozen by ruling D8 (`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

mutual
/-- **Well-formedness** (the uniqueness side conditions of T Prop `propstructure` (b)): in a type 2
code, `Q_lp` is trivial or of type 1 and the couple `𝒬₀` of the two chains is nontrivial. -/
def RegCpl.wf : RegCpl → Bool
  | .triv => true
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.wf && Q₂.wf && Q₃.wf
  | .type2 Xp Xm Qlp => Xp.wf && Xm.wf && Qlp.wf && !Qlp.isType2 && !(Xp.isNil && Xm.isNil)

/-- Well-formedness of a chain code (its couples are well formed). -/
def RegChain.wf : RegChain → Bool
  | .nil => true
  | .pair _ Qr Qg inner rest => Qr.wf && Qg.wf && inner.wf && rest.wf
end

end WaveTurbulence
