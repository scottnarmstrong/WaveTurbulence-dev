/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.InputsG3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.InputsDS
public import WaveTurbulence.Foundations.TVine.Struct.Final
public import WaveTurbulence.Foundations.TVine.Struct.LemmaP.Proof
public import WaveTurbulence.Foundations.TVine.Struct.Ladders.Final
/-! # The T-vine inputs of the H layers, discharged (packet L6, items H/I)

All T-vine combinatorics is proved by L3 (and its helpers) without inputs: N3 Thm 6 (iv) (`Ladders.ladders_holds`),
N3 Cor 1.16′ (`cor116Single_holds`), N2 Thm 1.15 (`subObjects_holds`), N3 Lemma P (`lemmaP`). So the layer classes
`Src.G3Inputs` (H-G3) and `Src.DSInputs` (H-DS) have global instances: a declaration with `[Src.G3Inputs V D]` or
`[Src.DSInputs V D]` is unconditional wherever this module is imported. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.Src

universe u v

/-- H-G3's input class, discharged by L3's ladder theorem. -/
instance g3Inputs_proved (V : Type u) (D : Type v) : G3Inputs V D := ⟨TVine.Struct.Ladders.ladders_holds⟩

/-- H-DS's input class, discharged by L3's Cor 1.16′, Thm 1.15 and Lemma P. -/
instance dsInputs_proved (V : Type u) (D : Type v) : DSInputs V D :=
  ⟨TVine.Struct.cor116Single_holds, TVine.Struct.subObjects_holds, TVine.Struct.lemmaP⟩

end WaveTurbulence.GammaLow.FinalCount.Src
