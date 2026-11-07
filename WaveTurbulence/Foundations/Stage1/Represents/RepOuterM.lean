/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepOuter

/-!
# S2 REPRESENTS: the per-mode outer form of a vine piece (INTERFACE v2, ruling R58)

After the mode expansion of every outer slot (VINE-D step 2) and the per-mode factorization (VINE-B♯) and class sum
(VINE-C), a σ-restricted τ-class sum is a weighted sum, over the outer slot modes, of `outerValM`:
* every replacement slot `s` of `G = G_sb` carries one mode: an amplitude `amp s` of its momentum and two integer
  frequencies `frq s`, one per clock argument;
* `route s i` says where the `i`-th clock of the slot lives: a clock of `G_sb` (`.inl y`), or the lower joint `b_j` of
  the unit `j` (`.inr j`, the slots at the lower external children `u21^j, u22^j` read `τ_{b_j}`, TARGET (redkg) L1726,
  finding F-LOWCLOCK);
* the frequencies routed to the unit `j` add up to its modulation `lam j` (`modLam`), and the unit factor is the modulated
  class kernel `HkM j (lam j)` (V5-CONT/W2 `twistedRecenteredModC … lam`), at the three exterior clocks `hclk j` and the
  four momenta `hmom j`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine MeasureTheory

variable {w d : ℕ}

/-- The modulation of the unit `j`: the sum of the slot frequencies routed to its lower joint. -/
noncomputable def modLam {G : Garden w} {J : Type} [DecidableEq J] (frq : ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) (j : J) : ℤ :=
  ∑ s, ∑ i, if route s i = Sum.inr j then frq s i else 0

/-- The phase of the clocks of `G_sb` carried by the slot modes (frequencies routed to a unit are omitted). -/
noncomputable def routedPhase {G : Garden w} {J : Type} (frq : ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) (tt : Fin w → ℝ) (τ : GBranch G.tree → ℝ) : ℂ :=
  ∏ s, ∏ i, match route s i with
    | Sum.inl y => Complex.exp (((Real.pi * (frq s i : ℝ) * clockOf G tt τ y : ℝ) : ℂ) * Complex.I)
    | Sum.inr _ => 1

/-- **The per-mode outer form of a vine piece** (INTERFACE v2, R58). -/
noncomputable def outerValM (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ)
    (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℝ) (hS : G.IsPlain)
    (amp : ReplacementSlot G → Mom d → ℂ) (frq : ReplacementSlot G → Fin 2 → ℤ)
    {J : Type} [Fintype J] [DecidableEq J] (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ G.order * G.zeta *
    ∑' z : GenDecoration G d roots 0, (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
      ∫ τ : GBranch G.tree → ℝ, (splicedTimeDomain G layer tt).indicator (fun τ =>
        phaseProd L γ δ G (cosetDecoration G L base z.1) τ *
          (∏ s, amp s (base + latticePoint L (z.1 (slotNode hS s)))) * routedPhase frq route tt τ *
          ∏ j, HkM j (modLam frq route j) (fun c => clockOf G tt τ (hclk j c))
            (fun c => base + latticePoint L (z.1 (hmom j c)))) τ

end WaveTurbulence.Represents
