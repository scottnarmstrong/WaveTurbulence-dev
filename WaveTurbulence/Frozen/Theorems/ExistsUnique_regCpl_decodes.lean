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
public import WaveTurbulence.Provider.ExistsUnique_regCpl_decodes

/-!
# existsUnique_regCpl_decodes

Wave B tier B2 (WaveB2-Regular.lean), source: T Prop `propstructure`. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **Structure theorem, couples** (T Prop `propstructure` (a), (b)): every regular couple has exactly
one well-formed code. -/
theorem existsUnique_regCpl_decodes (G : Garden 2) (hG : IsRegularCouple G) :
    ∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
