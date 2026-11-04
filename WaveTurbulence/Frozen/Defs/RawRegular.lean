/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.RawCpl
public import WaveTurbulence.Frozen.Defs.RawCplOpA
public import WaveTurbulence.Frozen.Defs.RawCplOpB
public import WaveTurbulence.Frozen.Defs.RawCplTree
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# RawRegular

Wave B tier B2 (WaveB2-Regular.lean), source: T Def `defreg`. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **Regular couples, source form** (T Def `defreg`): the raw data reachable from the trivial couple
`(•, •)` by finitely many operations A (at a leaf pair) and B (at a node). -/
inductive RawRegular : RawCpl → Prop
  | triv : RawRegular ((.leaf, .leaf), [((0, []), (1, []))])
  | opA {R : RawCpl} {x y : Fin 2 × Path} (c : MiniCplCode) :
      RawRegular R → (x, y) ∈ R.2 → RawRegular (R.opA x y c)
  | opB {R : RawCpl} {a : Fin 2 × Path} (m : MiniTreeCode) :
      RawRegular R → a.2 ∈ (R.tree a.1).nodes → RawRegular (R.opB a m)

end WaveTurbulence
