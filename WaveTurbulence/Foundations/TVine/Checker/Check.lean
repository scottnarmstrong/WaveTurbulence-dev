/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Params

/-!
# The per-instance check

`checkInst q` runs, on the block `genB q.1 q.2` with joints `jname`, `jname + 1`:
* `loopless`, `endsLt` (no loop; names below `32`), `pieceShapeB` (F2: piece shape), `interiorConnB` (F3: interior connected),
* `jointsAvoidB` (no sub-object contains a joint), `subFactsB` (F4, F5: types, gap freeness, removal connectivity
  of single sub-objects and of families).
Each instance is checked by `decide +kernel` in the instance modules.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

/-- The bitmask of the ends of a bond list. -/
def maskOf (es : Edges) : ℕ := es.foldl (fun acc e => acc ||| bit e.1 ||| bit e.2) 0

/-- No candidate sub-object contains a joint. -/
def jointsAvoidB (V : ℕ) (es : Edges) (J₁ J₂ : ℕ) : Bool :=
  (subObjects V es).all fun U => !mem J₁ U.S && !mem J₂ U.S

/-- All ends are below `32` (the bitmask width of `elems`). -/
def endsLt (es : Edges) : Bool := es.all fun e => e.1 < 32 && e.2 < 32

/-- **The check of one instance.** -/
def checkInst (q : CParam × JParam) : Bool :=
  let es := genB q.1 q.2
  let V := maskOf es
  let J := q.1.jname
  loopless es && endsLt es && pieceShapeB V es J (J + 1) && interiorConnB V es J (J + 1) && jointsAvoidB V es J (J + 1) && subFactsB V es

end WaveTurbulence.TVine.Checker
