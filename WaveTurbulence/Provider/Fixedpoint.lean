/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ATr
public import WaveTurbulence.Frozen.Defs.AnsatzAt
public import WaveTurbulence.Frozen.Defs.IsGaussianData
public import WaveTurbulence.Frozen.Defs.IsSymmetricEvent
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Lop
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.ZNorm
public import WaveTurbulence.Frozen.Defs.ZSpace

/-!
# Provider for `WaveTurbulence.fixedpoint`

The proof of the frozen anchor `WaveTurbulence.fixedpoint` (T Prop `fixedpoint`, L780–L794; WAVE-B v2 §4.3) is assembled here under the export
`WaveTurbulence.Provider.fixedpoint`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
