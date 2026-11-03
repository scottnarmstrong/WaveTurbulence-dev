/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.IsWKESolution
public import WaveTurbulence.Frozen.Defs.WeightedL2Norm

/-!
# Provider for `WaveTurbulence.wkelwp`

The proof of the frozen anchor `WaveTurbulence.wkelwp` (L598-L601 (Proposition 3.2, label wkelwp)) is assembled here under the export
`WaveTurbulence.Provider.wkelwp`. Quarantined while the anchor is `DRAFT_SORRY`: only the frozen anchor
may import this module.
-/

public section
