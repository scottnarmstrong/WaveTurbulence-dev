/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.IsASolution
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.KineticTime
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import WaveTurbulence.Frozen.Defs.ZNormOn

/-!
# Provider for `WaveTurbulence.nlsAkBridge`

The proof of the frozen anchor `WaveTurbulence.nlsAkBridge` (T L540–L566; L817–L819; WAVE-B v2 §4.4) is assembled here under the export
`WaveTurbulence.Provider.nlsAkBridge`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
