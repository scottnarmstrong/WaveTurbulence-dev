/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.AddrExt
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniCplCodePartner
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeGreen
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeLone
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeRed
public import WaveTurbulence.Frozen.Defs.RegChainLonePath
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.SlotSign
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# RegCpl.pairsAt, RegChain.pairsAt (mutual)

Wave B tier B2 (WaveB2-Regular.lean): one `mutual` block, frozen as one file because Lean cannot
split it; each declaration keeps its own manifest entry. Sources:
- `RegCpl.pairsAt`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850
- `RegChain.pairsAt`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850

Frozen by ruling D8 (`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

mutual
/-- **Decoding, leaf pairs** `(+ leaf, - leaf)` of a couple code whose `+` tree is rooted at `a` and
`-` tree at `b`. -/
def RegCpl.pairsAt {w : ℕ} : RegCpl → (Fin w × Path) → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .triv, a, b => [(a, b)]
  | .type1 c Q₁ Q₂ Q₃, a, b =>
    Q₁.pairsAt (addrExt a [0]) (addrExt b [c.partner 0]) ++
      Q₂.pairsAt (addrExt b [1]) (addrExt a [1]) ++
      Q₃.pairsAt (addrExt a [2]) (addrExt b [c.partner 2])
  | .type2 Xp Xm Qlp, a, b =>
    Xp.pairsAt 1 a ++ Xm.pairsAt (-1) b ++
      Qlp.pairsAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)

/-- **Decoding, leaf pairs of a chain** rooted at `a` with root sign `ζ` (the lone leaf excluded). -/
def RegChain.pairsAt {w : ℕ} : RegChain → ℤˣ → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .nil, _, _ => []
  | .pair m Qr Qg inner rest, ζ, a =>
    (if slotSign ζ m.red.1 = 1 then
        Qr.pairsAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ++
    (if slotSign ζ m.green.1 = 1 then
        Qg.pairsAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ++
    inner.pairsAt (slotSign ζ m.c) (addrExt a [m.c]) ++
    rest.pairsAt (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
end

end WaveTurbulence
