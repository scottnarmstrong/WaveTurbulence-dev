/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.FixMeasure
public import WaveTurbulence.Foundations.Stage1.Represents.RepOuterM

/-! # B3s MK-SLOTS: the per-mode outer form against a general time measure

`outerValMμ` is main's `Represents.outerValM` (INTERFACE v2, R58) with
* the time integral against an arbitrary measure `μ` on the time vectors of `G_sb` (pinned pieces use
  `fixMeasure fix`: Lebesgue on free atoms, Dirac masses at the pinned values), and
* a complex decoration weight `Zw` (pinned pieces carry the atom filters, the indicator and the removed phases there).

`outerValMμ_volume`: with `μ = volume` and a real weight it is main's `outerValM`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

/-- **The per-mode outer form against a time measure `μ`, with a complex decoration weight.** -/
def outerValMμ (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ)
    (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℂ) (hS : G.IsPlain)
    (μ : Measure (GBranch G.tree → ℝ))
    (amp : ReplacementSlot G → Mom d → ℂ) (frq : ReplacementSlot G → Fin 2 → ℤ)
    {J : Type} [Fintype J] [DecidableEq J] (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ G.order * G.zeta *
    ∑' z : GenDecoration G d roots 0, (splicedEpsilon G hinges z.1 : ℂ) * Zw z *
      ∫ τ, (splicedTimeDomain G layer tt).indicator (fun τ =>
        phaseProd L γ δ G (cosetDecoration G L base z.1) τ *
          (∏ s, amp s (base + latticePoint L (z.1 (slotNode hS s)))) * routedPhase frq route tt τ *
          ∏ j, HkM j (modLam frq route j) (fun c => clockOf G tt τ (hclk j c))
            (fun c => base + latticePoint L (z.1 (hmom j c)))) τ ∂μ

/-- With Lebesgue measure and a real weight, `outerValMμ` is main's `outerValM`. -/
theorem outerValMμ_volume (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ)
    (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℝ) (hS : G.IsPlain)
    (amp : ReplacementSlot G → Mom d → ℂ) (frq : ReplacementSlot G → Fin 2 → ℤ)
    {J : Type} [Fintype J] [DecidableEq J] (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) :
    outerValMμ G L γ δ base roots tt layer hinges (fun z => (Zw z : ℂ)) hS volume amp frq route hclk hmom HkM =
      outerValM G L γ δ base roots tt layer hinges Zw hS amp frq route hclk hmom HkM := rfl

end WaveTurbulence.Flower.MkSlots
