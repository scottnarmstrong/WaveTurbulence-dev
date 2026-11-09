/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.TVine.Struct.Final
public import WaveTurbulence.Foundations.TVine.Struct.SubObjBridge
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCExists
/-! # Discharge of L5a's L3 named inputs (packet L5a)

L3 proved the T-vine structure statements unconditionally (`TVine.Struct.Final`, `TVine.Struct.SubObjBridge`):
* `TVineF1Input` (N2 Thm 1.15 (F1)) is L3's `f1_mol` (L3's `Struct/Exact.lean` checks the restated type);
* `TVineStructInputs` (L5c's carried instance, = L3's `LayervineStatement ∧ PieceShapeStatement`) is
  `⟨layervine_holds, pieceShape_holds⟩`.
* `VinechainlemPrimeInput` (Lemma 8.1′ with DV′) is L3D's `TVine.Struct.Drawn.vinechainlemPrimeInput` applied to
  `f1_mol`.
All three are registered as global `Fact` instances, so every L5a/L5c theorem carrying them as instance arguments is
unconditional in them. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama

/-- **`TVineF1Input` holds** (L3's `TVine.Struct.f1_mol`). -/
theorem tvineF1Input_holds : TVineF1Input := fun _ _ _ _ hT => TVine.Struct.f1_mol hT

instance instFactTVineF1Input : Fact TVineF1Input := ⟨tvineF1Input_holds⟩

/-- **L5c's `TVineStructInputs` hold** (L3's `layervine_holds`, `pieceShape_holds`). -/
theorem tvineStructInputs_holds : Famc.ClassCount.TVineStructInputs :=
  ⟨TVine.Struct.layervine_holds, TVine.Struct.pieceShape_holds⟩

instance instFactTVineStructInputs : Fact Famc.ClassCount.TVineStructInputs := ⟨tvineStructInputs_holds⟩

/-- **`VinechainlemPrimeInput` holds** (L3D's Lemma 8.1′, from (F1)). -/
theorem vinechainlemPrimeInput_holds : VinechainlemPrimeInput :=
  TVine.Struct.Drawn.vinechainlemPrimeInput (fun M _ _ _ h => TVine.Struct.f1_mol (M := M) h)

instance instFactVinechainlemPrimeInput : Fact VinechainlemPrimeInput := ⟨vinechainlemPrimeInput_holds⟩

end WaveTurbulence.GammaLow.Fama
