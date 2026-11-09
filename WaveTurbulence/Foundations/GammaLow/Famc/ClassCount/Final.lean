/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.LayeringFinal
public import WaveTurbulence.Foundations.GammaLow.Famc.Discharge
/-! # The Stage 1 class count over `𝒱_γ` (packet L5c, item I)

TARGET (finalprooffin), L2236–L2252, for L5a's `𝒱_γ` Stage 1 pieces (`γ ≤ 1/2`): main's
`ClassCount.classCount_of_layeringLeg` (Stage1/ClassCount/Final.lean) over `𝒱_γ`. The three legs:
* `ClassCount.decodeSizeLeg` (main; family-free);
* `skeletonLegG_of_codeLeg skeletonCodeLegG` (molecule counts; the units are decoded through the `𝒱_γ` ingredient codes,
  including the T-vine branch `vine_chain_codeG`, item H);
* `layeringLegG` (layering counts; the transfer matrices of T-vine ingredients by layervine′, item D).
The L3 inputs are discharged (`Famc.Discharge`) except `LaddersInput` (N3 Theorem 6 (iv), used by layervine′). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount

/-- **The Stage 1 class count over `𝒱_γ`** (TARGET L2241–L2252), from L3's ladder statement. -/
theorem classCountG [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] (hLad : LaddersInput) :
    ClassCountStmtG := by
  have : Fact TVineStructInputs := ⟨tvineStructInputs_holds⟩
  have : Fact LayervineTVineImproved := ⟨layervineTVineImproved_of_ladders hLad⟩
  have : Fact LayervineTVineFirst := ⟨layervineTVineFirst_of_ladders hLad⟩
  exact classCountG_of_legs ClassCount.decodeSizeLeg (skeletonLegG_of_codeLeg skeletonCodeLegG) layeringLegG

end WaveTurbulence.GammaLow.Famc.ClassCount
