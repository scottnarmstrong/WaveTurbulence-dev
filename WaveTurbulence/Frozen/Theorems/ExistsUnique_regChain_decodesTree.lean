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
public import WaveTurbulence.Provider.ExistsUnique_regChain_decodesTree

/-!
# existsUnique_regChain_decodesTree

Wave B tier B2 (WaveB2-Regular.lean), source: T Prop `propstructure`. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **Structure theorem, trees** (T Prop `propstructure`, last part). -/
theorem existsUnique_regChain_decodesTree (G : Garden 1) (hG : IsRegularTree G) :
    ∃! X : RegChain, X.wf = true ∧ X.DecodesTree G :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.existsUnique_regChain_decodesTree
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
