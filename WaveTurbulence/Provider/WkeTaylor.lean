/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SNormR
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.WkeTaylorTerm

/-!
# Provider for `WaveTurbulence.wkeTaylor`

The proof of the frozen anchor `WaveTurbulence.wkeTaylor` (T (wketaylor); L752–L758; WAVE-B §5) is assembled here under the export
`WaveTurbulence.Provider.wkeTaylor`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
