/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Discharge
/-! # L5a-G: the T-vine structure instance used by L5c's `Famc/ClassCount/VineA` ports

L5c's ports of main's `Vine/A/VineUnitSelected*` etc. take `[Fact Famc.ClassCount.TVineStructInputs]`
(= L3's `LayervineStatement ∧ PieceShapeStatement`). Both are PROVED by L3 (`TVine.Struct.Final`), and L5c restates the
conjunction unconditionally (`Famc.tvineStructInputs_holds`, module `Famc.Discharge`). This global instance makes the
ported vine-case code (item G) use the proof, so no statement of item G carries it as a hypothesis. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama

/-- L3's T-vine structure (proved), as the instance consumed by L5c's ports. -/
instance tvineStructInputs_fact : Fact Famc.ClassCount.TVineStructInputs := ⟨Famc.tvineStructInputs_holds⟩

end WaveTurbulence.GammaLow.Fama
