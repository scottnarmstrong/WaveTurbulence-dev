/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveAssemble
public import WaveTurbulence.Foundations.TVine.Struct.Discharge

/-!
# M4 Theorem C from L2's roots

The three named inputs of `tvineChart_of_inputs` are L3's exact statements (`Chart.Inputs`), which L3 proves from L2's
`SizeBoundStatement` (N2 Lemma 1.8) and `PieceShapeBaseStatement` (F2) alone (`Struct.Discharge`:
`pieceShape_of_L2`, `layervine_of_L2`, `attach_of_L2`). Hence **M4 Theorem C is conditional only on these two L2
statements.**
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

/-- **M4 Theorem C (all sizes) from L2's roots.** -/
theorem tvineChart_of_L2 (hsize : Checker.SizeBoundStatement.{0})
    (hbase : Checker.PieceShapeBaseStatement.{0}) : TVineChartStatement :=
  tvineChart_of_inputs (Struct.pieceShape_of_L2 hsize hbase) (Struct.layervine_of_L2 hsize hbase)
    (Struct.attach_of_L2 hsize hbase)

end WaveTurbulence.TVine.Chart
