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
# RegCpl.linksAt, RegChain.linksAt (mutual)

Wave B tier B2 (WaveB2-Regular.lean): one `mutual` block, frozen as one file because Lean cannot
split it; each declaration keeps its own manifest entry. Sources:
- `RegCpl.linksAt`: T Prop `deflink`, L874–L882
- `RegChain.linksAt`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850

Frozen by ruling D8 (`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

mutual
/-- **Links** of a couple code (T Prop `deflink`, L874–L882), as `(chosen, other)` pairs of branching
node addresses; the `+` tree is rooted at `a`, the `-` tree at `b`. Type 1: the two roots (the `+`
root chosen) and recursively; type 2: `(𝔫_a^ε, 𝔫_b^ε)` for every pair `{a,b} ∈ 𝒫^ε` (`𝔫_a` chosen) and
recursively. -/
def RegCpl.linksAt {w : ℕ} : RegCpl → (Fin w × Path) → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .triv, _, _ => []
  | .type1 c Q₁ Q₂ Q₃, a, b =>
    (a, b) :: (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0]) ++
      Q₂.linksAt (addrExt b [1]) (addrExt a [1]) ++
      Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2]))
  | .type2 Xp Xm Qlp, a, b =>
    Xp.linksAt 1 a ++ Xm.linksAt (-1) b ++
      Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)

/-- Links of a chain rooted at `a` with root sign `ζ` (and of its couples). -/
def RegChain.linksAt {w : ℕ} : RegChain → ℤˣ → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .nil, _, _ => []
  | .pair m Qr Qg inner rest, ζ, a =>
    (a, addrExt a ([m.c] ++ inner.lonePath)) ::
    ((if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ++
    (if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ++
    inner.linksAt (slotSign ζ m.c) (addrExt a [m.c]) ++
    rest.linksAt (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])))
end

end WaveTurbulence
