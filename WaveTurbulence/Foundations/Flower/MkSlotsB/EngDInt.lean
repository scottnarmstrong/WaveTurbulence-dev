/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.OuterFix
public import WaveTurbulence.Foundations.Flower.MkSlots.Slice
public import WaveTurbulence.Foundations.Flower.SelRes.Triv

/-! # B3s-HELPER3 B3 (1): the assembled expansion on a general time domain

Domain-generic twin of `MkSlots/EngInt.lean` (B3s's pinned engine, step 2). Main's `AsmCtxH` is reused unchanged
(built with the unpinned hinge hypothesis `hHk`); only what reads the time domain is twinned:
* `gIHD A D`: main's summand `gIH` (RepH8) with the indicator of an arbitrary set `D` of time vectors;
* `hasSum_gIHD`: copy of main's `hasSum_gIH`, using main's pointwise `hasSum_assembledH` with the hinge HasSum and the
  slot boxes assumed ON `D` (`hboxD`, `hHkD`), so it holds at every `τ`;
* the integral lemmas of `EngInt` with `μ D ≤ 1` in place of `μ (splicedTimeDomain) ≤ 1`.
Against `fixMeasure fix` the engine integrates over `D := Dom ∩ pinSet fix` (`pinSet fix`: the pinned coordinates
equal the pins); `fixMeasure fix` only sees `pinSet fix` (`integral_fixMeasure_inter_pinSet`), so the outer form on
`Dom` and the kernel's relaxed domain agree under `hsliceD` (`integral_fixMeasure_indicatorD`, `value_eqHMD`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsB

/-! ## The pinned slice -/

/-- The pinned slice: time vectors whose pinned coordinates are the pins. -/
def pinSet {ι : Type*} (fix : ι → Option ℝ) : Set (ι → ℝ) := {τ | ∀ i v, fix i = some v → τ i = v}

theorem extendFixI_mem_pinSet {ι : Type*} (fix : ι → Option ℝ) (τ : {i // fix i = none} → ℝ) :
    extendFixI fix τ ∈ pinSet fix := fun _ _ h => extendFixI_some fix τ h

/-- `fixMeasure fix` only sees the pinned slice. -/
theorem integral_fixMeasure_inter_pinSet {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (fix : ι → Option ℝ) (Dom : Set (ι → ℝ)) (f : (ι → ℝ) → E) :
    ∫ τ, (Dom ∩ pinSet fix).indicator f τ ∂(fixMeasure fix) = ∫ τ, Dom.indicator f τ ∂(fixMeasure fix) := by
  rw [integral_fixMeasure, integral_fixMeasure]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  by_cases h : extendFixI fix τ ∈ Dom
  · have h' : extendFixI fix τ ∈ Dom ∩ pinSet fix := ⟨h, extendFixI_mem_pinSet fix τ⟩
    rw [indicator_of_mem h', indicator_of_mem h]
  · have h' : extendFixI fix τ ∉ Dom ∩ pinSet fix := fun h' => h h'.1
    rw [indicator_of_notMem h', indicator_of_notMem h]

variable {w d : ℕ}

/-! ## The summand on a general domain -/

variable {S : Garden w} (A : AsmCtxH S d)

section Generic

variable (D : Set (GBranch S.tree → ℝ))

variable (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ)) (ind : (GNode S.tree → Mom d) → ℝ)

variable {filt ind} (hfilt : ∀ a q, filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ ind k ∧ ind k ≤ 1)
include hfilt hind

end Generic

/-! ## One assembled mode on `Dom ∩ pinSet fix` is a pinned spliced kernel -/

section Pinned

variable (fix : GBranch S.tree → Option ℝ) (filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ))
  (ind : (GNode S.tree → Mom d) → ℝ) (lb : GBranch S.tree → Option ℝ) (Dom : Set (GBranch S.tree → ℝ))
  (hsliceD : ∀ τ : {b : GBranch S.tree // fix b = none} → ℝ,
    S.extendFix fix τ ∈ Dom ↔ S.extendFix fix τ ∈ splicedTimeDomainFix S A.layer0 A.tt fix ∩ splicedLBDomain lb)

variable {filt ind}

end Pinned

end WaveTurbulence.Flower.MkSlotsB
