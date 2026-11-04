/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.AddrExt
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeGreen
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeLone
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeRed
public import WaveTurbulence.Frozen.Defs.Node3
public import WaveTurbulence.Frozen.Defs.NodeSign
public import WaveTurbulence.Frozen.Defs.RawCpl
public import WaveTurbulence.Frozen.Defs.RawCplMapTree
public import WaveTurbulence.Frozen.Defs.RawCplOrient
public import WaveTurbulence.Frozen.Defs.RawCplRelocate
public import WaveTurbulence.Frozen.Defs.RawCplTree
public import WaveTurbulence.Frozen.Defs.SlotSign
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TTreeSetAt
public import WaveTurbulence.Frozen.Defs.TTreeSubtreeAt

/-!
# RawCpl.opB

Wave B tier B2 (WaveB2-Regular.lean), source: T Def `defreg`; WAVE-B §3.3. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

namespace RawCpl

/-- **Operation B** at the node `a` with mini-tree code `m`: the subtree `S` at `a` is detached, `a`
becomes the root `ρ` of the mini-tree, `S` is re-attached at its lone leaf (keeping `a`'s sign), and
the mini-tree's red and green leaf pairs are new pairs (T Def `defreg`; WAVE-B §3.3, figure-defs §5:
B at a leaf keeps the leaf's pair). -/
def opB (R : RawCpl) (a : Fin 2 × Path) (m : MiniTreeCode) : RawCpl :=
  let S := (R.tree a.1).subtreeAt a.2
  let mini := node3 fun i => if i = m.c then node3 (fun k => if k = m.lone then S else .leaf) else .leaf
  let ζ : ℤˣ := nodeSign ![1, -1] a
  (R.mapTree a.1 (fun T => T.setAt a.2 mini),
    R.2.map (fun q => (relocate a m.c m.lone q.1, relocate a m.c m.lone q.2)) ++
      [orient (addrExt a [m.red.1]) (slotSign ζ m.red.1) (addrExt a [m.c, m.red.2]),
       orient (addrExt a [m.green.1]) (slotSign ζ m.green.1) (addrExt a [m.c, m.green.2])])

end RawCpl
end WaveTurbulence
