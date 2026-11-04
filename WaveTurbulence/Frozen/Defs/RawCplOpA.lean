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
public import WaveTurbulence.Frozen.Defs.RawCpl
public import WaveTurbulence.Frozen.Defs.RawCplMapTree
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TTreeSetAt

/-!
# RawCpl.opA

Wave B tier B2 (WaveB2-Regular.lean), source: T Def `defreg`; WAVE-B §3.3. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

namespace RawCpl

/-- **Operation A** at the leaf pair `(x, y)` (`x` the `+` leaf) with mini-couple code `c`: both leaves
become order-1 trees whose six leaves are paired as the mini-couple of code `c`, with `x` in the role
of the `+` root (T Def `defreg`; WAVE-B §3.3). -/
def opA (R : RawCpl) (x y : Fin 2 × Path) (c : MiniCplCode) : RawCpl :=
  let t3 : TTree := .node .leaf .leaf .leaf
  let R' : RawCpl := (R.mapTree x.1 (fun T => T.setAt x.2 t3), R.2)
  ((R'.mapTree y.1 (fun T => T.setAt y.2 t3)),
    R.2.erase (x, y) ++ [(addrExt x [0], addrExt y [c.partner 0]), (addrExt y [1], addrExt x [1]),
      (addrExt x [2], addrExt y [c.partner 2])])

end RawCpl
end WaveTurbulence
