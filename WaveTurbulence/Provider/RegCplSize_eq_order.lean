/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeOrders

/-!
# Provider for `WaveTurbulence.RegCpl.size_eq_order` (B2 anchor O5, B2-CL-22)

The proof of the frozen anchor `WaveTurbulence.RegCpl.size_eq_order` (WaveB2-Regular.lean §4) is assembled here under the export
`WaveTurbulence.Provider.size_eq_order`. The statement is the anchor's, with the data binders implicit and
the hypotheses `by assumption` autoParams (the `wkelwp` pattern), so the anchor body is the bare
`by exact WaveTurbulence.Provider.size_eq_order`. The proof is wt-resonant's REG-STRUCT
(`/home/scott/wt-scratch/reg-struct/B2CharacterizationProofs.lean`, `f2817fe8…`). Quarantined while the anchor is
`DRAFT_SORRY`: only the frozen anchor may import this module.
-/

public section

namespace WaveTurbulence.Provider

theorem size_eq_order {Q : RegCpl} {G : Garden 2} (h : Q.Decodes G := by assumption) : G.order = Q.size :=
  Reg.size_eq_order h

end WaveTurbulence.Provider
