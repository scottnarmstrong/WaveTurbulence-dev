/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.OuterFix

/-! # B3s MK-SLOTS: the per-mode outer form on a general time domain (shared interface for β/δ/γ)

`outerValMμD … Dom …` is `outerValMμ` with the time domain `splicedTimeDomain G layer tt` replaced by an arbitrary set
`Dom` of time vectors of `G_sb`. Pieces with adjacent pins (milestone β: patterns `dParent`, `dChild`, `dRoot`) use
the RELAXED pinned domain `Dom := splicedTimeDomainFix G layer tt fix` (order constraints only for pairs with a free
member, windows and root truncation only at free atoms), on which the unpinned domain is empty.

* `outerValMμD` (the definition), `outerValMμ_eq_D` (`Dom = splicedTimeDomain G layer tt` is `outerValMμ`, by `rfl`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

/-- **The per-mode outer form on a time domain `Dom`, against a time measure `μ`, with a complex decoration weight.**
-/
def outerValMμD (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (Dom : Set (GBranch G.tree → ℝ))
    (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℂ) (hS : G.IsPlain)
    (μ : Measure (GBranch G.tree → ℝ))
    (amp : ReplacementSlot G → Mom d → ℂ) (frq : ReplacementSlot G → Fin 2 → ℤ)
    {J : Type} [Fintype J] [DecidableEq J] (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ G.order * G.zeta *
    ∑' z : GenDecoration G d roots 0, (splicedEpsilon G hinges z.1 : ℂ) * Zw z *
      ∫ τ, Dom.indicator (fun τ =>
        phaseProd L γ δ G (cosetDecoration G L base z.1) τ *
          (∏ s, amp s (base + latticePoint L (z.1 (slotNode hS s)))) * routedPhase frq route tt τ *
          ∏ j, HkM j (modLam frq route j) (fun c => clockOf G tt τ (hclk j c))
            (fun c => base + latticePoint L (z.1 (hmom j c)))) τ ∂μ

/-- With the unpinned spliced domain, `outerValMμD` is `outerValMμ`. -/
theorem outerValMμ_eq_D (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ)
    (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℂ) (hS : G.IsPlain)
    (μ : Measure (GBranch G.tree → ℝ))
    (amp : ReplacementSlot G → Mom d → ℂ) (frq : ReplacementSlot G → Fin 2 → ℤ)
    {J : Type} [Fintype J] [DecidableEq J] (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) :
    outerValMμ G L γ δ base roots tt layer hinges Zw hS μ amp frq route hclk hmom HkM =
      outerValMμD G L γ δ base roots tt (splicedTimeDomain G layer tt) hinges Zw hS μ amp frq route hclk hmom HkM :=
  rfl

end WaveTurbulence.Flower.MkSlots
