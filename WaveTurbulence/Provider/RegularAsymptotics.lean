/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InputRemainder
public import WaveTurbulence.Frozen.Defs.KQstar
public import WaveTurbulence.Frozen.Defs.KTstar
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RegBound
public import WaveTurbulence.Frozen.Defs.RegChainApp
public import WaveTurbulence.Frozen.Defs.RegChainDecodesTree
public import WaveTurbulence.Frozen.Defs.RegChainJBtree
public import WaveTurbulence.Frozen.Defs.RegChainLonePath
public import WaveTurbulence.Frozen.Defs.RegChainTreeLinks
public import WaveTurbulence.Frozen.Defs.RegCplApp
public import WaveTurbulence.Frozen.Defs.RegCplDecodes
public import WaveTurbulence.Frozen.Defs.RegCplDominantRegChainDominant
public import WaveTurbulence.Frozen.Defs.RegCplJBRegChainJBchain
public import WaveTurbulence.Frozen.Defs.RegCplLinks
public import WaveTurbulence.Frozen.Defs.RegCplMstarRegChainNstar
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplSizeRegChainSize
public import WaveTurbulence.Frozen.Defs.RegCplWfRegChainWf
public import WaveTurbulence.Frozen.Defs.SNormR
public import WaveTurbulence.Frozen.Defs.SpecialSets
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TimeBox
public import WaveTurbulence.Frozen.Defs.TimeBoxGt
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.WkeTaylorTerm
public import WaveTurbulence.Frozen.Defs.XNorm00Restr
public import WaveTurbulence.Frozen.Defs.XNormRestr

/-!
# Provider for `WaveTurbulence.regularAsymptotics`

The proof of the frozen anchor `WaveTurbulence.regularAsymptotics` (L1145–L1232; WAVE-B v2 §4.11; T (regref1-3); DH21 Lemma 7.3) is assembled here under the export
`WaveTurbulence.Provider.regularAsymptotics`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
