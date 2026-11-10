/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedNode

/-! # B3s MK-SLOTS: a pinned root factors out of the upper clock (ruling R184, F-B3s-7)

On a plain layered garden with per-root upper clocks `top`, the clock `top j` enters the time domain only through the
constraint on the root branch of tree `j` (`parentClockWith` reads `top` only at roots). If that root `r` is pinned at
`sv`, then on the pinned slice
`τ ∈ kDomain (top) ↔ sv < top j0 ∧ τ ∈ kDomain (top with any value u₀ > sv at j0)`
(`mem_coreTimeDomainW_rootPinned`), and the pinned weighted kernel factors:
`kernelNodeWF … (top) … = [sv < top j0] · kernelNodeWF … (top[j0 ↦ u₀]) …` (`kernelNodeWF_rootPinned`).
For a cap couple whose top node is the pinned capped flower parent this splits the slot kernel into the indicator
`[s < ts 0]` (moved to a lower bound of the parent atom) and a kernel independent of its upper clock. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

/-- `fixMeasure`-almost every time vector takes the pinned value at a pinned coordinate. -/
theorem ae_fixMeasure_pinned {ι : Type*} [Fintype ι] (fix : ι → Option ℝ) {i : ι} {v : ℝ} (h : fix i = some v) :
    ∀ᵐ τ ∂(fixMeasure fix), τ i = v := by
  rw [ae_iff]
  have : {τ : ι → ℝ | ¬ τ i = v} = Function.eval i ⁻¹' ({v}ᶜ : Set ℝ) := by ext τ; simp
  rw [this]
  refine Measure.pi_eval_preimage_null _ ?_
  simp only [fixFactor, h, Option.elim]
  rw [Measure.dirac_apply' _ (measurableSet_singleton v).compl]
  simp

end WaveTurbulence.Flower.MkSlots
