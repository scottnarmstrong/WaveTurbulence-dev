/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ReverseRange

/-!
# Provider for `WaveTurbulence.RegCpl.exists_decodes` (B2 anchor O1, B2-CL-22)

The proof of the frozen anchor `WaveTurbulence.RegCpl.exists_decodes` (WaveB2-Regular.lean §4) is assembled here under the export
`WaveTurbulence.Provider.exists_decodes`. The statement is the anchor's, with the data binders implicit and
the hypotheses `by assumption` autoParams (the `wkelwp` pattern), so the anchor body is the bare
`by exact WaveTurbulence.Provider.exists_decodes`. The proof is wt-resonant's REG-STRUCT
(`/home/scott/wt-scratch/reg-struct/B2CharacterizationProofs.lean`, `f2817fe8…`). Quarantined while the anchor is
`DRAFT_SORRY`: only the frozen anchor may import this module.
-/

public section

namespace WaveTurbulence.Provider

theorem exists_decodes {Q : RegCpl} (hQ : Q.wf = true := by assumption) :
    ∃ G : Garden 2, Q.Decodes G ∧ IsRegularCouple G :=
  Reg.wf_code_exists_regular_decodes Q hQ

end WaveTurbulence.Provider
