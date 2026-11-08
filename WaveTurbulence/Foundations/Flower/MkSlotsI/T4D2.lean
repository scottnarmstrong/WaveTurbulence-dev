/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBRInteg
public import WaveTurbulence.Foundations.Flower.MkSlotsI.T4D

/-! # B3s MK-SLOTS (final assembly): the pinned list-T4 on a general time domain

The τ-class sum of the members' per-mode outer values is the outer value with the class kernels. α's
`MkSlots/IntT4.lean` states this (T4) for `outerValMμ` (fixed layered domain, any time measure, complex decoration
weight) with the `Option ℝ` top filters of V5W; B3-2's `MkUnitsL/ClassL.lean` states it for main's `outerValM`
(Lebesgue, real decoration weight) with the LIST top filters `SU : J₀ → List ℝ`. Both proofs only use main's generic
`VineC.sum_outer_core`, which holds for every measure and every time domain. Here they are combined for the
domain-generic pinned outer form `outerValMμD … Dom …` (arbitrary time domain `Dom`, time measure `μ`, complex
decoration weight `Zw`), whose integrand is β's `outerIntegrandMD`.

* `sum_classU_outerValMμD` (α's `sum_classU_outerValMμ` on the domain `Dom`);
* **`weightedClassFactorizationμDL`** (B3-2's `WeightedClassFactorizationL` for `outerValMμD`, unit kernels
  `unitRecenteredFWL`, class kernels `twistedRecenteredFWL`).

Copied by source (see `COPIED-SHA256SUMS`). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkSlotsI
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 TTree MeasureTheory
open WaveTurbulence.VineC WaveTurbulence.Flower.V5W
open WaveTurbulence.Flower.V5W2L (twistedLocalKernelFWL twistedRecenteredFWL unitRecenteredFWL)
open WaveTurbulence.Flower.MkSlots (outerValMμD)
open WaveTurbulence.Flower.MkSlotsB (outerIntegrandMD)
open WaveTurbulence.Flower.MkUnitsL (unitKernelFWL_classProd)

variable {w : ℕ}

/-- **Mode-dependent decoration weight** `Zw i ξ` (e.g. the node partition `chiX X` of a centre-indexed mode); proof of `weightedClassFactorizationμDL` verbatim.  **Pinned list-T4 on a general time domain.** The τ-class sum of the members' per-mode outer values
`outerValMμD … Dom …` (time domain `Dom`, time measure `μ`, complex decoration weight `Zw`), each with its OWN weighted
unit kernels `unitRecenteredFWL` (unit `j` carries the weight `gU j` and the list top filter `SU j`), equals the outer
value with the weighted class kernels `twistedRecenteredFWL` of the units. Hypotheses as in B3-2's
`WeightedClassFactorizationL` (the VINE-B♯ factorization `hV`, the mode summability `hξ`, and the `μ`-integrability
`hint` and decoration summability `hsm` of the members' integrands `outerIntegrandMD`). -/
theorem weightedClassFactorizationμDLZ {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    {U₀ : J₀ → Finset (GBranch S.tree)} {a₀ b₀ : J₀ → GBranch S.tree} {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)}
    {n₀ : J₀ → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j)) (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j'))
    (hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool} (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = (unitsStart B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) {I : Type*} [Fintype I] (sgn : I → ℂ) {Ξ : Type*} (Wt : I → Ξ → ℂ) {d : ℕ}
    (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (Dom : Set (GBranch G.tree → ℝ)) (hinges : Finset (GBranch G.tree)) (Zw : I → Ξ → GenDecoration G d roots 0 → ℂ)
    (hG : G.IsPlain) (μ : Measure (GBranch G.tree → ℝ))
    (amp : I → Ξ → ReplacementSlot G → Mom d → ℂ) (frq : I → Ξ → ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀) (hclk : J₀ → Fin 3 → ClkSrc G)
    (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (gU : J₀ → Mom d → ℂ) (SU : J₀ → List ℝ)
    (hV : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      V y.1.layered = ∑ i, sgn i * ∑' ξ, Wt i ξ *
        outerValMμD G L γ δ base roots tt Dom hinges (Zw i ξ) hG μ (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)))
    (hξ : ∀ i, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun ξ => Wt i ξ *
        outerValMμD G L γ δ base roots tt Dom hinges (Zw i ξ) hG μ (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    (hint : ∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ z, Integrable (outerIntegrandMD G L γ δ base roots tt Dom hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
          (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z) μ)
    (hsm : ∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * Zw i ξ z *
          ∫ τ, outerIntegrandMD G L γ δ base roots tt Dom hG (amp i ξ) (frq i ξ) route hclk hmom
            (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
              (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ ∂μ)) :
    ∑ LG ∈ T, V LG = ∑ i, sgn i * ∑' ξ, Wt i ξ *
      outerValMμD G L γ δ base roots tt Dom hinges (Zw i ξ) hG μ (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => twistedRecenteredFWL p (gU j) (SU j) S (a₀ j)
          (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
          L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) := by
  rw [sum_layered_eq_sum_classU (Us := unitsSplit B₀) (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime
    (unitsRegion B₀ hdisj₀) T hT V, Finset.sum_congr rfl hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (hξ i)]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hfg : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ (j : J₀) (lam : ℤ) (t : Fin 3 → ℝ) (k : Fin 4 → Mom d),
        unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3) =
          recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
              ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
            twistedLocalKernelFWL p (gU j) (SU j)
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).1
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).2
              L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
    intro y hy j lam t k
    obtain ⟨M, _, hR⟩ := (mem_classU hprime).mp hy
    unfold unitRecenteredFWL
    rw [hR.sign_upper j, unitKernelFWL_classProd hprime ((mem_classU hprime).mp hy) j]
    rfl
  rw [sum_classU_outerValMμD (Us := unitsSplit B₀) (p := p) (kind := kind)
    (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime (unitsRegion B₀ hdisj₀) G L γ δ base roots tt Dom hinges (Zw i ξ)
    hG μ (amp i ξ) (frq i ξ) route hclk hmom _
    (fun j lam t k x => recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
        ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
      twistedLocalKernelFWL p (gU j) (SU j) x.1 x.2 L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
        (k 0) (k 1) (k 2) (k 3))
    hfg (hint i ξ) (hsm i ξ)]
  congr 1
  funext j lam t k
  unfold twistedRecenteredFWL
  exact (Finset.mul_sum _ _ _).symm

end WaveTurbulence.Flower.MkSlotsI
