/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.SlotObl

/-! # B3s-HELPER7 (general assembly): the slot times of a pinned relaxed core time lie in `genSlotBox`

On the pinned slice of β's relaxed core domain `coreTimeDomainWR layer0 tt fixC` (free branches in their layer
windows, `τ b < parent clock` whenever `b` or its clock is free), with pins in their windows `(layer, layer + 1]` and
root times in `[p, p + 1]`, the two clock times of every slot lie in the general slot box `genSlotBox`: a pinned
clock is at its pin, and if some clock is free the point is in main's `slotBox` (closed windows; strict order of a
chain slot's clocks, kept by the relaxed domain because a clock is free). This is VINE-B♯'s `hbox` for the box
`genSlotBox` (`slotTs_mem_genSlotBox`).

* `clkPin_clkOfNode_eq_none_iff`: the clock of a node is unpinned iff it is `clockFree`;
* `clockOf_mem_Icc_of_pinned`: every clock time is in its closed layer window;
* **`slotTs_mem_genSlotBox`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents

namespace WaveTurbulence.Flower.MkSlotsI

variable {w : ℕ} {S : Garden w}

/-- The clock of a node is unpinned iff the node is `clockFree`. -/
theorem clkPin_clkOfNode_eq_none_iff (tt : Fin w → ℝ) (fixC : GBranch S.tree → Option ℝ) (ν : GNode S.tree) :
    clkPin tt fixC (clkOfNode S ν) = none ↔ MkSlotsB.clockFree fixC ν := by
  unfold clkOfNode MkSlotsB.clockFree
  rcases nodeToSlot ν with j | ⟨b, i⟩
  · simp [clkPin]
  · simp [clkPin]

/-- Every clock time of a pinned relaxed core time is in the closed window of its clock layer. -/
theorem clockOf_mem_Icc_of_pinned (p : ℕ) (layer0 : GBranch S.tree → ℕ) (tt : Fin w → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (fixC : GBranch S.tree → Option ℝ)
    (hval : ∀ b v, fixC b = some v → (layer0 b : ℝ) < v ∧ v ≤ layer0 b + 1)
    (τ : GBranch S.tree → ℝ) (hpin : ∀ b v, fixC b = some v → τ b = v)
    (hτ : τ ∈ MkSlotsB.coreTimeDomainWR layer0 tt fixC) (y : ClkSrc S) :
    clockOf S tt τ y ∈ Icc (clkLayer p layer0 y : ℝ) (clkLayer p layer0 y + 1) := by
  rcases y with j | b
  · exact htt j
  · show τ b ∈ Icc (layer0 b : ℝ) (layer0 b + 1)
    rcases hfb : fixC b with _ | v
    · obtain ⟨h1, h2, -⟩ := (hτ b).1 hfb
      exact ⟨h1.le, h2.le⟩
    · rw [hpin b v hfb]
      obtain ⟨h1, h2⟩ := hval b v hfb
      exact ⟨h1.le, h2⟩

/-- **The slot times of a pinned relaxed core time lie in the general slot box.** -/
theorem slotTs_mem_genSlotBox (p : ℕ) (layer0 : GBranch S.tree → ℕ) (hS : S.IsPlain) (tt : Fin w → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (fixC : GBranch S.tree → Option ℝ)
    (hval : ∀ b v, fixC b = some v → (layer0 b : ℝ) < v ∧ v ≤ layer0 b + 1)
    (τ : GBranch S.tree → ℝ) (hpin : ∀ b v, fixC b = some v → τ b = v)
    (hτ : τ ∈ MkSlotsB.coreTimeDomainWR layer0 tt fixC) (sl : ReplacementSlot S) :
    slotTs hS tt τ sl ∈ genSlotBox p layer0 hS tt fixC sl := by
  have hI := clockOf_mem_Icc_of_pinned p layer0 tt htt fixC hval τ hpin hτ
  refine ⟨fun i v hv => ?_, fun hfree => ?_⟩
  · show clockOf S tt τ (argSrc hS sl i) = v
    generalize argSrc hS sl i = y at hv ⊢
    rcases y with j | b
    · simp only [clkPin, Option.some.injEq] at hv
      exact hv
    · exact hpin b v hv
  · cases sl with
    | inl q =>
      exact ⟨hI _, hI _⟩
    | inr b =>
      refine ⟨⟨hI _, hI _⟩, ?_⟩
      show clockOf S tt τ (argSrc hS (.inr b) 1) < clockOf S tt τ (argSrc hS (.inr b) 0)
      simp only [argSrc, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [← parentClockWith_eq_clockOf]
      refine (hτ b).2 ?_
      obtain ⟨i, hi⟩ := hfree
      fin_cases i
      · right
        have hi' : clkPin tt fixC (clkOfNode S b.toNode) = none := by simpa [argSrc] using hi
        exact (clkPin_clkOfNode_eq_none_iff tt fixC b.toNode).1 hi'
      · left
        simpa [argSrc, clkPin] using hi

end WaveTurbulence.Flower.MkSlotsI
