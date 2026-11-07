/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD1
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlots2M
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB18
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: per-member facts (F-box)

`sourceShape_slotBox`: the time box of the outer slot `iota s'` of a class member is the representative's.
`sourceShape_hbox`: the member's core time domain maps the outer slots into that box.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.RegRedLeaf

variable {p : ℕ} {kind : Bool}

theorem sourceShape_slotBox {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain) (s : ReplacementSlot a.fullProfile.piece.gap.garden) :
    slotBox p (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode) y.1.plain
        ((sourceShape a y hy).iota y.1.plain hG s) =
      slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1
        ((profileShape a).iota a.prime.prime.1 hG s) := by
  rcases s with q | c
  · have h0 := sourceShape_clkLayer a y hy hG (Sum.inl q) 0
    have h1 := sourceShape_clkLayer a y hy hG (Sum.inl q) 1
    simp only [SpliceShape.iota] at h0 h1 ⊢
    simp only [slotBox, h0, h1]
  · have h0 := sourceShape_clkLayer a y hy hG (Sum.inr c) 0
    have h1 := sourceShape_clkLayer a y hy hG (Sum.inr c) 1
    simp only [SpliceShape.iota] at h0 h1 ⊢
    simp only [slotBox, h0, h1]


theorem sourceShape_hbox {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) :
    ∀ τ ∈ coreTimeDomainW (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode) tt,
      ∀ s, slotTs y.1.plain tt τ ((sourceShape a y hy).iota y.1.plain hG s) ∈
        slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1
          ((profileShape a).iota a.prime.prime.1 hG s) := by
  intro τ hτ s
  rw [← sourceShape_slotBox a y hy hG s]
  exact slotTs_mem_slotBox p _ y.1.plain tt htt τ (coreTimeDomainW_subset_spliced _ _ _ hτ) _

end WaveTurbulence.Represents
