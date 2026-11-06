/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamBasePhysicalExistence
public import WaveTurbulenceVineParam.VineParamFinal
import Mathlib.Tactic

/-! # The M9 named obligation `VINEPARAM`

Every actual vine of every type (arbitrary rung insertions, F72 `m = 1` for type II,
F79 signed nonlinear cores) has the full source chart of `Contract.lean`. The proof is
the expanded-template induction `exists_physical_expanded` over the checked
normalized base catalogue `exists_physical_base_chart`.
-/

public section
namespace WaveTurbulence.Vine.Param

theorem vineparam : VineParamContract.VINEPARAM :=
  vineparam_of_base (fun X {_m} A hU hdeg joint a b ha hb =>
    exists_physical_base_chart X A hU hdeg joint a b ha hb)

end WaveTurbulence.Vine.Param
