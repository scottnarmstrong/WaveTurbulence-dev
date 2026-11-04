/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.IsRegularCouple
public import WaveTurbulence.Frozen.Defs.RegCplDecodes
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplWfRegChainWf
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Provider.RegCplExists_decodes

/-!
# RegCpl.exists_decodes

Wave B tier B2 (WaveB2-Regular.lean), source: (file) WAVE-B v2 §2.7; L826–L829; L848–L850. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- Decoding a well-formed code gives a regular couple carrier. -/
theorem RegCpl.exists_decodes (Q : RegCpl) (hQ : Q.wf = true) :
    ∃ G : Garden 2, Q.Decodes G ∧ IsRegularCouple G :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.exists_decodes
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
