/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepBr1
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the time boxes of the replacement slots
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed Set

variable {w : ℕ} {S : Garden w}

/-- The time box of a slot: `[q,q+1] × [q',q'+1]`, `q, q'` the layers of its two clock sources (trees: with `t > s`). -/
def slotBox (p : ℕ) (layer0 : GBranch S.tree → ℕ) (hS : S.IsPlain) :
    ReplacementSlot S → Set (Fin 2 → ℝ)
  | .inl p' => timeBox (clkLayer p layer0 (argSrc hS (.inl p') 0) : ℝ) (clkLayer p layer0 (argSrc hS (.inl p') 1))
  | .inr b => timeBoxGt (clkLayer p layer0 (argSrc hS (.inr b) 0) : ℝ) (clkLayer p layer0 (argSrc hS (.inr b) 1))

theorem clock_mem_Icc (p : ℕ) (layer0 : GBranch S.tree → ℕ) (tt : Fin w → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (τ : GBranch S.tree → ℝ)
    (hτ : ∀ v, τ v ∈ Icc (layer0 v : ℝ) (layer0 v + 1)) (y : ClkSrc S) :
    clockOf S tt τ y ∈ Icc (clkLayer p layer0 y : ℝ) (clkLayer p layer0 y + 1) := by
  rcases y with j | b
  · exact htt j
  · exact hτ b

theorem slotTs_mem_slotBox (p : ℕ) (layer0 : GBranch S.tree → ℕ) (hS : S.IsPlain) (tt : Fin w → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (τ : GBranch S.tree → ℝ)
    (hτ : τ ∈ splicedTimeDomain S layer0 tt) (s : ReplacementSlot S) :
    slotTs hS tt τ s ∈ slotBox p layer0 hS s := by
  obtain ⟨h1, h2, h3⟩ := hτ
  have hc := clock_mem_Icc p layer0 tt htt τ h1
  cases s with
  | inl p' => exact ⟨hc _, hc _⟩
  | inr b =>
    refine ⟨⟨hc _, hc _⟩, ?_⟩
    have hlt := (clock_iff tt τ).2 ⟨h2, h3⟩ b
    rw [parentClockWith_eq_clockOf] at hlt
    show clockOf S tt τ (argSrc hS (.inr b) 1) < clockOf S tt τ (argSrc hS (.inr b) 0)
    simpa [argSrc, clockOf] using hlt

end WaveTurbulence.Represents
