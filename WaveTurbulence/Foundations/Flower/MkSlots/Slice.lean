/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.FixMeasure
public import WaveTurbulence.Foundations.Flower.MkSlots.Data
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerP1Stub

/-! # B3s MK-SLOTS: the pinned slice of the unpinned time domain

When every pinned value satisfies the unpinned constraints of its branch (strictly inside its layer window, positive,
below its upper time) and no two pinned branches are parent and child (`AdmissiblePins`), the frozen pinned domain
`kDomainFix` and the unpinned domain `kDomain` agree on the pinned slice. Then main's pinned leaf kernel term
`FlowerP1.kernelLeavesFixTerm` is the unpinned-domain integral against `fixMeasure`
(`kernelLeavesFixTerm_eq_fixMeasure`), the form consumed by the pinned reduction.

Milestone α: the intrinsic pins of plain patterns (capped flower parents at `s ∈ (p, t)`) are admissible
(`admissiblePins_plain`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

theorem extendFix_eq_extendFixI (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) : G.extendFix fix τ = extendFixI fix τ := by
  funext b
  unfold Garden.extendFix extendFixI
  rfl

end WaveTurbulence.Flower.MkSlots
