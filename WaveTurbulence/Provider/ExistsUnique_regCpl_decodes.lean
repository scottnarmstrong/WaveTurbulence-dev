/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeUniqueness

/-!
# Provider for `WaveTurbulence.existsUnique_regCpl_decodes` (B2 anchor O2, B2-CL-22)

The proof of the frozen anchor `WaveTurbulence.existsUnique_regCpl_decodes` (WaveB2-Regular.lean §4) is assembled here under the export
`WaveTurbulence.Provider.existsUnique_regCpl_decodes`. The statement is the anchor's, with the data binders implicit and
the hypotheses `by assumption` autoParams (the `wkelwp` pattern), so the anchor body is the bare
`by exact WaveTurbulence.Provider.existsUnique_regCpl_decodes`. The proof is wt-resonant's REG-STRUCT
(`/home/scott/wt-scratch/reg-struct/B2CharacterizationProofs.lean`, `f2817fe8…`). Quarantined while the anchor is
`DRAFT_SORRY`: only the frozen anchor may import this module.
-/

public section

namespace WaveTurbulence.Provider

theorem existsUnique_regCpl_decodes {G : Garden 2} (hG : IsRegularCouple G := by assumption) :
    ∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G := by
  obtain ⟨Q, hQ, hunique⟩ := Reg.isRegularCouple_existsUnique_structure G hG
  refine ⟨Q.1, ⟨Q.2, hQ⟩, ?_⟩
  intro C hC
  exact congrArg Subtype.val (hunique ⟨C, hC.1⟩ hC.2)

end WaveTurbulence.Provider
