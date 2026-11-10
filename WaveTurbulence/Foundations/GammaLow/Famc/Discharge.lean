/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.TVine.Struct.Final
public import WaveTurbulence.Foundations.TVine.Struct.Ladders.Final
public import WaveTurbulence.Foundations.GammaLow.Famc.Coarse.Gate
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Gate
public import WaveTurbulence.Foundations.GammaLow.Fama.Gate
public import WaveTurbulence.Foundations.GammaLow.Famc.Layervine.Improved
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
/-! # Discharge of L5c's L3 named inputs (L3's `TVine.Struct.Final`, proved unconditionally)

L3 proved its T-vine structure statements (`TVine.Struct.Final`: `subObjects_holds`, `pieceShape_holds`,
`layervine_holds`; `TVine.Struct.Ladders.Final`: `ladders_holds`, N3 Theorem 6 (iv)). Every L3 named input of L5c is
discharged here, and the exports that carried them are restated unconditionally. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.Induct WaveTurbulence.LGSpine

theorem pieceShapeInput_holds : PieceShapeInput := TVine.Struct.pieceShape_holds
theorem layervineInput_holds : LayervineInput := TVine.Struct.layervine_holds
theorem laddersInput_holds : LaddersInput := TVine.Struct.Ladders.ladders_holds
theorem tvineStructInputs_holds : ClassCount.TVineStructInputs :=
  ⟨TVine.Struct.layervine_holds, TVine.Struct.pieceShape_holds⟩

/-- **layervine′, first bound**, from L3's ladder statement only. -/
theorem layervineTVineFirst_of_ladders (hLad : LaddersInput) : LayervineTVineFirst :=
  layervineTVineFirst hLad pieceShapeInput_holds

/-- **layervine′, improved bound**, from L3's ladder statement only. -/
theorem layervineTVineImproved_of_ladders (hLad : LaddersInput) : LayervineTVineImproved :=
  layervineTVineImproved hLad pieceShapeInput_holds layervineInput_holds

/-- **layervine′, first bound, unconditional.** -/
theorem layervineTVineFirst_holds : LayervineTVineFirst := layervineTVineFirst_of_ladders laddersInput_holds

/-- **layervine′, improved bound, unconditional.** -/
theorem layervineTVineImproved_holds : LayervineTVineImproved := layervineTVineImproved_of_ladders laddersInput_holds

end WaveTurbulence.GammaLow.Famc
