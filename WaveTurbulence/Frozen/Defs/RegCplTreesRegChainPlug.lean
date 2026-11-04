/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeLone
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeRed
public import WaveTurbulence.Frozen.Defs.Node3
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.SlotSign
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TreeOfSign

/-!
# RegCpl.trees, RegChain.plug (mutual)

Wave B tier B2 (WaveB2-Regular.lean): one `mutual` block, frozen as one file because Lean cannot
split it; each declaration keeps its own manifest entry. Sources:
- `RegCpl.trees`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850
- `RegChain.plug`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850

Frozen by ruling D8 (`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

mutual
/-- **Decoding, trees**: `Q.trees = (𝒯⁺, 𝒯⁻)`. -/
def RegCpl.trees : RegCpl → TTree × TTree
  | .triv => (.leaf, .leaf)
  | .type1 c Q₁ Q₂ Q₃ =>
    (.node Q₁.trees.1 Q₂.trees.2 Q₃.trees.1,
      if c = 0 then .node Q₁.trees.2 Q₂.trees.1 Q₃.trees.2
      else .node Q₃.trees.2 Q₂.trees.1 Q₁.trees.2)
  | .type2 Xp Xm Qlp => (Xp.plug 1 Qlp.trees.1, Xm.plug (-1) Qlp.trees.2)

/-- **Decoding, chains**: the tree of a chain whose root `𝔫_1` has sign `ζ`, with the subtree `h`
plugged at the lone-leaf position. -/
def RegChain.plug : RegChain → ℤˣ → TTree → TTree
  | .nil, _, h => h
  | .pair m Qr Qg inner rest, ζ, h =>
    node3 fun i =>
      if i = m.c then
        inner.plug (slotSign ζ m.c) (node3 fun k =>
          if k = m.lone then rest.plug (slotSign (slotSign ζ m.c) k) h
          else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
          else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k))
      else if i = m.red.1 then treeOfSign Qr.trees (slotSign ζ i)
      else treeOfSign Qg.trees (slotSign ζ i)
end

end WaveTurbulence
