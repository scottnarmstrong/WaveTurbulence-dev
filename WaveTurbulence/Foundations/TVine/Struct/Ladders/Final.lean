/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Ladders.Main
public import WaveTurbulence.Foundations.TVine.Struct.Final

/-!
# N3 Theorem 6 (iv), unconditional (packet L3-LAD)

`ladders_of` applied to L3's unconditional `layervine_holds` and `pieceShape_holds` (`Struct/Final.lean`; L1 and L2
discharged).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Struct.Ladders

universe u v

/-- **N3 Theorem 6 (iv)** (`LaddersStatement`), unconditional. -/
theorem ladders_holds : LaddersStatement.{u, v} :=
  ladders_of layervine_holds.{u, v} pieceShape_holds.{u, v}

end WaveTurbulence.TVine.Struct.Ladders
