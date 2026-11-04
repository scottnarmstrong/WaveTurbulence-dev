/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.IsRegularTree
public import WaveTurbulence.Frozen.Defs.RegChainDecodesTree
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplWfRegChainWf
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# Provider for `WaveTurbulence.RegChain.exists_decodesTree`

The proof of the frozen anchor `WaveTurbulence.RegChain.exists_decodesTree` ((file) WAVE-B v2 §2.7; L826–L829; L848–L850) is assembled here under the export
`WaveTurbulence.Provider.exists_decodesTree`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
