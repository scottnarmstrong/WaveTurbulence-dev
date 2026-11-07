/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.Stage1Gate

/-!
# B1b (ruling R156): the truncation-free Stage-1 carrier

Main's Stage-1 producer reads only four clauses of `LGSpine.Stage1Carries`: canonicity, the order, the balanced
signature and the width-2 non-regularity (B0 S-STAGE1MK §5.1: the top truncation `IsTrunc` is never used on the
producer path).  `Stage1CarriesW` is that truncation-free carrier (B0 probe, verbatim); the producer's carrier
hypotheses are weakened to it (the `…W` / `…Mk` forms of the producer theorems), and main's own gate keeps
`Stage1Carries` through `stage1CarriesW_of_stage1Carries`.  The marked carrier (`MkCarries`, top truncation
`N_{p+1}^4`) of the world implies it together with the non-regularity clause.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1Mk
open WaveTurbulence.LGSpine WaveTurbulence.Induct

/-- The Stage-1 carrier without the truncation clause (R156): canonical, of order `N`, balanced, and not a regular
couple at width `2`. -/
def Stage1CarriesW (P : WTParams) (p N : ℕ) {w : ℕ} (LG : LayeredGarden w) : Prop :=
  IsCanonGC (p + 1) LG ∧ LG.garden.order = N ∧ IsBalancedSig LG.garden.sig ∧
    (∀ h : w = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2))

/-- Main's carrier implies the truncation-free one. -/
theorem stage1CarriesW_of_stage1Carries {P : WTParams} {p N w : ℕ} {LG : LayeredGarden w}
    (h : Stage1Carries P p N LG) : Stage1CarriesW P p N LG :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end WaveTurbulence.Stage1Mk
