/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Iso
public import WaveTurbulence.Foundations.TVine.Struct.SubObjBridge
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCExists

/-! # L8-I-SLOTS: discharge of the L3 named inputs carried by the I-SLOTS declarations

Every I-SLOTS declaration carries the family instances of `Stage1MK/CONVENTIONS.md`:
`[Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]`. All three now hold
unconditionally:
* `Fama.TVineF1Input` (N2 Thm 1.15 (F1)) is L3's `TVine.Struct.f1_mol` (`TVine.Struct.SubObjBridge`; L3's
  `Struct/Exact.lean` checks the restated type);
* `Fama.VinechainlemPrimeInput` (N2 N6, DH23 Lemma 8.1′) is L3D's `TVine.Struct.Drawn.vinechainlemPrimeInput`
  applied to (F1);
* `Fama.TVineIsoInvariant` is L5a's `Fama.tvineIsoInvariant` (already a global instance in `Fama.Vine.Iso`).
The first two are registered here as global `Fact` instances, so every I-SLOTS theorem is unconditional in them for
any importer (L5a's `Fama.Discharge` registers the same `TVineF1Input` fact; duplicate `Fact` instances of a
proposition are harmless). `Exact.lean` checks the exports with no family hypothesis. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Flower

/-- **`Fama.TVineF1Input` holds** (L3's `TVine.Struct.f1_mol`, N2 Theorem 1.15 (F1)). -/
theorem tvineF1Input_holdsSlots : Fama.TVineF1Input := fun _ _ _ _ hT => TVine.Struct.f1_mol hT

/-- **`Fama.VinechainlemPrimeInput` holds** (L3D's Lemma 8.1′, `TVine.Struct.Drawn.vinechainlemPrimeInput`, from
(F1)). -/
theorem vinechainlemPrimeInput_holdsSlots : Fama.VinechainlemPrimeInput :=
  TVine.Struct.Drawn.vinechainlemPrimeInput tvineF1Input_holdsSlots

instance instFactTVineF1InputSlots : Fact Fama.TVineF1Input := ⟨tvineF1Input_holdsSlots⟩

instance instFactVinechainlemPrimeInputSlots : Fact Fama.VinechainlemPrimeInput :=
  ⟨vinechainlemPrimeInput_holdsSlots⟩

/-- All three family facts are available as instances. -/
example : Fact Fama.TVineF1Input ∧ Fact Fama.VinechainlemPrimeInput ∧ Fact Fama.TVineIsoInvariant :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end WaveTurbulence.GammaLow.Flower
