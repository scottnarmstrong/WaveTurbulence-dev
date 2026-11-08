/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLbDom
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBR1
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK

/-! # B3s-HELPER3 (R187): the lower-bound domains are the world's `splicedLBDomain`

B1's `lbDomC` (core lower bounds) and B2's `lbDomR` (`G_sb` lower bounds) have the body of DEFS lb2's
`MkDefs.splicedLBDomain` (`{t | ∀ v x, lb v = some x → x < t v}`); the identities are definitional. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.MkSlotsB

theorem lbDomC_eq_splicedLBDomain {w : ℕ} {G : Garden w} (lb : GBranch G.tree → Option ℝ) :
    lbDomC lb = MkDefs.splicedLBDomain lb := rfl

theorem lbDomR_eq_splicedLBDomain {w : ℕ} {G : Garden w} (lb : GBranch G.tree → Option ℝ) :
    lbDomR lb = MkDefs.splicedLBDomain lb := rfl

end WaveTurbulence.Flower.MkSlotsB
