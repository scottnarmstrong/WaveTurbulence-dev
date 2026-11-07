/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepOuterM
public import WaveTurbulence.Foundations.Stage1.Represents.RepH5

/-!
# S2 REPRESENTS: a per-mode outer form is an outer form with single-mode slot kernels (INTERFACE v2 → VINE-D)

Under natural routing (each clock of a slot is either its own clock in `G_sb` or the lower joint of a unit), the per-mode
outer form `outerValM` is the outer form `outerVal` whose slot kernels are the single modes `amp s · e^{πi frqR s · slotTs}`
(`frqR`: the frequencies of the clocks that stay in `G_sb`) and whose vine factors are the modulated kernels at
`modLam`.  This is the entry point of the VINE-D engine (`AsmCtxH`, `repIntC_of_asmH`) for one mode.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine MeasureTheory
  WaveTurbulence.VineEstS3.FS

variable {w d : ℕ}

/-- The frequencies of the clocks that stay in `G_sb`. -/
def frqR {G : Garden w} {J : Type} (frq : ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) : ReplacementSlot G → Fin 2 → ℤ :=
  fun s i => match route s i with
    | Sum.inl _ => frq s i
    | Sum.inr _ => 0

theorem routedPhase_eq {G : Garden w} (hS : G.IsPlain) {J : Type} (frq : ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (tt : Fin w → ℝ) (τ : GBranch G.tree → ℝ) :
    routedPhase frq route tt τ = ∏ s, fsPhase (frqR frq route s) (slotTs hS tt τ s) := by
  unfold routedPhase
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [fsPhase_eq_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases hroute s i with h | ⟨j, h⟩
  · simp only [frqR, h, slotTs]
  · simp only [frqR, h, Int.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero]

theorem outerValM_eq_outerVal (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree))
    (Zw : GenDecoration G d roots 0 → ℝ) (hS : G.IsPlain) (amp : ReplacementSlot G → Mom d → ℂ)
    (frq : ReplacementSlot G → Fin 2 → ℤ) {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) :
    outerValM G L γ δ base roots tt layer hinges Zw hS amp frq route hclk hmom HkM =
      outerVal G hS L γ δ base roots tt layer hinges Zw
        (fun s ts k => amp s k * fsPhase (frqR frq route s) ts) hclk hmom
        (fun j => HkM j (modLam frq route j)) := by
  unfold outerValM outerVal
  congr 1
  refine tsum_congr fun z => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hτ : τ ∈ splicedTimeDomain G layer tt
  · simp only [Set.indicator_of_mem hτ]
    rw [routedPhase_eq hS frq route hroute tt τ, Finset.prod_mul_distrib]
    ring
  · simp only [Set.indicator_of_notMem hτ]

end WaveTurbulence.Represents
