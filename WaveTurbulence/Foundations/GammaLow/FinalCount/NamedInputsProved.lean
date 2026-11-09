/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.NamedInputs
public import WaveTurbulence.Foundations.TVine.Struct.Final
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Main
/-! # L6's named inputs, discharged (packet L6)

The three L3 named inputs of `NamedInputs.lean` are proved unconditionally by L3 / L3D (`TVine.Struct.Final`,
`TVine.Struct.Drawn.Main`; exact checks in `TVine/Struct/Exact.lean`): N2 Prop 1.17(b) (`pieceShape_holds`), N3
Cor 1.16′ (`cor116Single_holds`), N2 Lemma 5.2 (`drawnTVine`). Consumers of L6's inputs (L6's helpers) import this
module instead of taking them as hypotheses. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount

universe u v

/-- N2 Prop 1.17(b), the pieces of a T-vine (L3's `pieceShape_holds`). -/
theorem tvinePiecesInput_proved : TVinePiecesInput.{u, v} := TVine.Struct.pieceShape_holds

/-- N3 Cor 1.16′ (1)–(3), the single-vine container (L3's `cor116Single_holds`). -/
theorem cor116PrimeInput_proved : Cor116PrimeInput.{u, v} := TVine.Struct.cor116Single_holds

/-- N2 Lemma 5.2, drawn vines of types (III)–(VIII) are T-vines (L3D's `drawnTVine`). -/
theorem drawnTVineInput_proved : DrawnTVineInput.{u, v} := TVine.Struct.Drawn.drawnTVine

end WaveTurbulence.GammaLow.FinalCount
