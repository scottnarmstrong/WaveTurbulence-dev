/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLeaves

/-! # B3s-HELPER3 (B1): the relaxed reduction specializes to the unpinned-domain one (`_one`)

When every constraint that the relaxed domains drop holds strictly at the pinned values — pins strictly inside their
layer windows and strictly below the upper times, and STRICTLY monotone along ancestry (`StrictPins`; α's pins, at
most one per tree, satisfy it vacuously in the monotonicity part) — the relaxed and the unpinned domains agree on the
pinned slices of the garden, the core and every native slot. Then, with unit slot weights `Θs ≡ 1`, the relaxed
reduction `kernelLeaves_skeleton_reduction_selNWFMR` is, statement for statement,
`MkSlotsW.kernelLeaves_skeleton_reduction_selNWFM` (`kernelLeaves_skeleton_reduction_selNWFMR_one`).

(Non-strict equal pins — β's `dParent`/`dChild` — are exactly the case where the unpinned domains are empty on the
pinned slice and only the relaxed statement is meaningful.)

* `mem_kDomainR_iff_kDomain`, `mem_coreTimeDomainWR_iff`: relaxed = unpinned when the dropped constraints hold;
* `StrictPins`, `StrictPins.relax`;
* `kernelLeavesSelNWFMR_one_eq`, `slotFnGWFR_one_eq`, **`kernelLeaves_skeleton_reduction_selNWFMR_one`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlotsB
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlots WaveTurbulence.LGSpine

variable {w : ℕ}

/-! ### Relaxed = unpinned when the dropped constraints hold -/

/-! ### Strict pins -/

/-- The pinned slice. -/
def OnSlice {ι : Type*} (fix : ι → Option ℝ) (τ : ι → ℝ) : Prop := ∀ b v, fix b = some v → τ b = v

theorem ae_onSlice {ι : Type*} [Fintype ι] (fix : ι → Option ℝ) : ∀ᵐ τ ∂(fixMeasure fix), OnSlice fix τ := by
  filter_upwards [ae_pinnedAt fix] with τ h
  exact h.pin

/-! ### The slices of a reconstruction -/

section Recon

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (tt : Fin w → ℝ) (fixG : GBranch (D.forest hS) → Option ℝ)

end Recon

/-! ### Unit slot weights and strict pins: the unpinned-domain statement -/

section One

variable {w d : ℕ}

theorem kernelNodeWR_one_eq (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Dom : Set (GBranch LG.garden.tree → ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (fix : GBranch LG.garden.tree → Option ℝ) (h : ∀ τ, OnSlice fix τ → (τ ∈ Dom ↔ τ ∈ kDomain LG up s)) :
    kernelNodeWR L γ δ LG A m Dom k₀ nroot nfl (fun _ => 1) fix = kernelNodeWF L γ δ LG A m up s k₀ nroot nfl fix := by
  unfold kernelNodeWR kernelNodeWF
  congr 1
  refine tsum_congr fun κ => ?_
  rw [mul_one]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [ae_onSlice fix] with τ hτ
  by_cases h1 : τ ∈ kDomain LG up s
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem ((h τ hτ).mpr h1)]
  · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h' => h1 ((h τ hτ).mp h'))]

end One

end WaveTurbulence.Flower.MkSlotsB
