/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeIncomparable
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerGarden
public import WaveTurbulence.Frozen.Defs.GardenIsPlain
public import WaveTurbulence.Frozen.Defs.InstDecidableEqGNode
public import WaveTurbulence.Frozen.Defs.IsCanonC
public import WaveTurbulence.Frozen.Defs.IsCanonG
public import WaveTurbulence.Frozen.Defs.IsCanonGC
public import WaveTurbulence.Frozen.Defs.IsCanonH
public import WaveTurbulence.Frozen.Defs.IsCouple
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachLinkedOn
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachNodes
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonInd
public import WaveTurbulence.Frozen.Defs.LayeredGardenRoots
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopDecomp
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopDecompWith

/-!
# Provider for `WaveTurbulence.canonicalCharacterization`

The proof of the frozen anchor `WaveTurbulence.canonicalCharacterization` (T Def `defcanon`, L657–L668; L888–L897; T Def `defgtr`; T L2288) is assembled here under the export
`WaveTurbulence.Provider.canonicalCharacterization`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
