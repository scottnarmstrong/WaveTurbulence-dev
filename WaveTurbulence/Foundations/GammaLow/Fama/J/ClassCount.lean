/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.J.Assembly
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Final
public import WaveTurbulence.Foundations.TVine.Struct.Ladders.Final
/-! # The gate with L5c's class count bound (packet L5a, item J)

L5c's `classCountG` (item I) with L3's ladder theorem (`TVine.Struct.Ladders.ladders_holds`, N3 Thm 6 (iv)) closes
the class-count input of `stage1ReductionGateLow_of`; only the vine-case statements of item G remain. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence WaveTurbulence.LGSpine

/-- **The class count over `𝒱_γ`**, unconditional (L5c's `classCountG` with L3's ladders). -/
theorem classCountStmtG_holds : Famc.ClassCount.ClassCountStmtG :=
  Famc.ClassCount.classCountG TVine.Struct.Ladders.ladders_holds

/-- **`Stage1ReductionGateLow` from the vine case** (item G's four statements). -/
theorem stage1ReductionGateLow_of_vineCase (hnv : WTPrefix NoVineRepresentsLow)
    (hvine : WTPrefix VineCaseRepresentsLow) (hnvm : LargeConstantMonotone NoVineRepresentsLow)
    (hvm : LargeConstantMonotone VineCaseRepresentsLow) : Stage1ReductionGateLow :=
  stage1ReductionGateLow_of classCountStmtG_holds hnv hvine hnvm hvm

end WaveTurbulence.GammaLow.Fama
