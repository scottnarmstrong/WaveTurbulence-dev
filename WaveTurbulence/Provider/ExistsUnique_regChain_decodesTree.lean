/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.SourceTreeDecoding

/-!
# Provider for `WaveTurbulence.existsUnique_regChain_decodesTree` (B2 anchor O4, B2-CL-22)

The proof of the frozen anchor `WaveTurbulence.existsUnique_regChain_decodesTree` (WaveB2-Regular.lean §4) is assembled here under the export
`WaveTurbulence.Provider.existsUnique_regChain_decodesTree`. The statement is the anchor's, with the data binders implicit and
the hypotheses `by assumption` autoParams (the `wkelwp` pattern), so the anchor body is the bare
`by exact WaveTurbulence.Provider.existsUnique_regChain_decodesTree`. The proof is wt-resonant's REG-STRUCT
(`/home/scott/wt-scratch/reg-struct/B2CharacterizationProofs.lean`, `f2817fe8…`). Quarantined while the anchor is
`DRAFT_SORRY`: only the frozen anchor may import this module.
-/

public section

namespace WaveTurbulence.Provider

theorem existsUnique_regChain_decodesTree {G : Garden 1} (hG : IsRegularTree G := by assumption) :
    ∃! X : RegChain, X.wf = true ∧ X.DecodesTree G := by
  obtain ⟨X, hX, hunique⟩ := Reg.isRegularTree_existsUnique_structure G hG
  refine ⟨X.1, ⟨X.2, hX⟩, ?_⟩
  intro Y hY
  exact congrArg Subtype.val (hunique ⟨Y, hY.1⟩ hY.2)

end WaveTurbulence.Provider
