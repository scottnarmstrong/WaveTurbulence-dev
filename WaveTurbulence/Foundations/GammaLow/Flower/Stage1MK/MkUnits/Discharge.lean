/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Iso
public import WaveTurbulence.Foundations.TVine.Struct.SubObjBridge
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCExists

/-! # L8-I-UNITS: discharge of the L3 named inputs carried by item I-UNITS

The item-I port conventions (`Stage1MK/CONVENTIONS.md`) carry L5a's named inputs as instance arguments
`[Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]`. All three hold now:
* `Fama.TVineF1Input` (N2 Thm 1.15 (F1)) is L3's `TVine.Struct.f1_mol` (`TVine/Struct/SubObjBridge.lean`; L3's
  `Struct/Exact.lean` checks the restated type);
* `Fama.VinechainlemPrimeInput` (N2 N6, Lemma 8.1′) is L3D's `TVine.Struct.Drawn.vinechainlemPrimeInput`
  (`TVine/Struct/Drawn/VCExists.lean`) applied to the same F1 (L3D's `VC.TVineF1Input` has the body of
  `Fama.TVineF1Input`);
* `Fama.TVineIsoInvariant` is L5a's `Fama.tvineIsoInvariant`, registered as an instance in `Fama/Vine/Iso.lean`.
The first two are registered here as global `Fact` instances (L5a's `Fama/Discharge.lean` registers the first one too,
once published; duplicate `Fact` instances are harmless), so the MkUnits modules no longer take them as arguments. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Flower

/-- **`Fama.TVineF1Input` holds** (L3's `TVine.Struct.f1_mol`, N2 Thm 1.15 (F1)). -/
theorem mkUnits_tvineF1Input_holds : Fama.TVineF1Input := fun _ _ _ _ hT => TVine.Struct.f1_mol hT

/-- **`Fama.VinechainlemPrimeInput` holds** (L3D's Lemma 8.1′ from F1). -/
theorem mkUnits_vinechainlemPrimeInput_holds : Fama.VinechainlemPrimeInput :=
  TVine.Struct.Drawn.vinechainlemPrimeInput fun _ _ _ _ hT => TVine.Struct.f1_mol hT

instance mkUnits_instFactTVineF1Input : Fact Fama.TVineF1Input := ⟨mkUnits_tvineF1Input_holds⟩

instance mkUnits_instFactVinechainlemPrimeInput : Fact Fama.VinechainlemPrimeInput :=
  ⟨mkUnits_vinechainlemPrimeInput_holds⟩

example : Fact Fama.TVineIsoInvariant := inferInstance

end WaveTurbulence.GammaLow.Flower
