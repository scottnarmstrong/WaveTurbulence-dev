/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Chi0Vec
public import WaveTurbulence.Frozen.Defs.EZ
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# Provider for `WaveTurbulence.quadExpSum3`

The proof of the frozen anchor `WaveTurbulence.quadExpSum3` (T Lemma `lemcubic`, L1554–L1593) is assembled here under the export
`WaveTurbulence.Provider.quadExpSum3`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
