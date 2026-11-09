/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.J.ClassCount
public import WaveTurbulence.Foundations.GammaLow.Fama.VineCaseProof
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Final
public import WaveTurbulence.Foundations.TVine.Chart.Unconditional
public import WaveTurbulence.Foundations.TVine.Struct.Ladders.Final
/-! # The Stage 1 reduction gate for `γ ≤ 1/2` (packet L5a, final) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama

/-- **`Stage1ReductionGateLow`** (rows 7–10 of the spine over `𝒱_γ`, `0 < γ ≤ 1/2`), unconditional: L5c's class count
with L3's ladder theorem, L5a-G's vine case with L4's Theorem C, L5c's subpro′, L3/L3D's structure (`Fama.Discharge`). -/
theorem stage1ReductionGateLow : Stage1ReductionGateLow :=
  stage1ReductionGateLow_of_vineCase noVineLow vineCaseLow_uncond noVineRepresentsLow_mono vineCaseRepresentsLow_mono

end WaveTurbulence.GammaLow.Fama
