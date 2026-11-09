/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Roots
public import WaveTurbulence.Foundations.TVine.Checker.SizeBound2
public import WaveTurbulence.Foundations.TVine.Checker.BasePieces

/-!
# M4 Theorem C, unconditional

L2 proved its two roots (`Checker.sizeBound`: N2 Lemma 1.8; `Checker.pieceShapeBase`: F2), so the named inputs of this
area (L3's exact statements, via `Struct.Discharge`) and M4 Theorem C hold with no hypotheses.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

/-- N2 Prop 1.17(b) (the named input `PieceShapeInput`), unconditional. -/
theorem pieceShapeInput_holds : PieceShapeInput :=
  Struct.pieceShape_of_L2 Checker.sizeBound Checker.pieceShapeBase

/-- N3 Theorem 6 (i)–(iii) (the named input `LayervineInput`), unconditional. -/
theorem layervineInput_holds : LayervineInput :=
  Struct.layervine_of_L2 Checker.sizeBound Checker.pieceShapeBase

/-- M4 Lemma A (the named input `AttachInput`), unconditional. -/
theorem attachInput_holds : AttachInput :=
  Struct.attach_of_L2 Checker.sizeBound Checker.pieceShapeBase

/-- **M4 Theorem C (all sizes)**: every T-vine has a de-indexed normal full chart whose groups are its pieces. -/
theorem tvineChart_holds : TVineChartStatement :=
  tvineChart_of_L2 Checker.sizeBound Checker.pieceShapeBase

/-- Theorem C without the groups. -/
theorem tvineChartExists_holds : TVineChartExists := tvineChart_holds.exists

/-- **The `𝒱_γ` chart contract**, unconditional. -/
theorem vineGammaChart_holds : VineGammaChartStatement :=
  vineGammaChart_of_L2 Checker.sizeBound Checker.pieceShapeBase

/-- The cell decompositions, unconditional. -/
theorem decompExists_holds : DecompExists :=
  decompExists_of_L2 Checker.sizeBound Checker.pieceShapeBase

end WaveTurbulence.TVine.Chart
