/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible
public import WaveTurbulence.Frozen.Defs.SumintDatumExpr
public import WaveTurbulence.Frozen.Defs.SumintDatumM0
public import WaveTurbulence.Frozen.Defs.SumintDatumM1
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeM
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefixA
public import WaveTurbulence.Frozen.Defs.XNorm00Restr

/-!
# Provider for `WaveTurbulence.sumint`

The proof of the frozen anchor `WaveTurbulence.sumint` (T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6) is assembled here under the export
`WaveTurbulence.Provider.sumint`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
