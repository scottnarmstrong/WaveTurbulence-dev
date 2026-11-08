/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.OuterFix
public import WaveTurbulence.Foundations.Flower.V5W.Foreign

/-! # B3s MK-SLOTS (integration): the pinned class sum (T4 against a time measure)

The τ-class sum of the members' per-mode outer values is the outer value with the class kernels. Main's
`VineC.sum_classU_outerValM` and V5W's `weightedClassFactorization` (T4) are stated for `outerValM` (Lebesgue time
measure, real decoration weight); their proofs only use the generic `VineC.sum_outer_core`, which holds for every
measure. Here they are restated for `outerValMμ` (any time measure `μ`, e.g. the pinned `fixMeasure fix` of a piece,
and a complex decoration weight `Zw`, e.g. the piece's atom weight times the gap selection).

* `sum_classU_outerValMμ` (main's `sum_classU_outerValM`);
* **`weightedClassFactorizationμ`** (V5W's `weightedClassFactorization`, copied by source, see `COPIED-SHA256SUMS`). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.MkSlots
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 TTree MeasureTheory
open WaveTurbulence.VineC WaveTurbulence.Flower.V5W

variable {w : ℕ}

section Outer
variable {ι : Type*} {J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {κ : J → Type*}
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] {Us : UnitSplit ι J κ} {p : ℕ} {kind : Bool}

-- [copied] main `Vine/C/VCOuter.lean` lines 156–186 (`sum_classU_outerValM`), with `outerValM` → `outerValMμ`
-- (time measure `μ`, complex `Zw`), see COPIED-SHA256SUMS.
/-- **The class sum of the per-mode outer form against a time measure.** -/
theorem sum_classU_outerValMμ {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) {d : ℕ} (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree))
    (Zw : GenDecoration G d roots 0 → ℂ) (hS : G.IsPlain) (μ : Measure (GBranch G.tree → ℝ))
    (amp : ReplacementSlot G → Mom d → ℂ)
    (frq : ReplacementSlot G → Fin 2 → ℤ) (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
    (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (HkMy : UState w Us → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ)
    (gk : ∀ j, ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) →
      (Σ X : FamilyReconstruction w (κ j), ChainAt X.skeleton X.family) → ℂ)
    (hfg : ∀ y ∈ classU Us p kind A us, ∀ j lam t k, HkMy y j lam t k = gk j lam t k (classProd Us p kind A us y j))
    (hint : ∀ y ∈ classU Us p kind A us, ∀ z,
      Integrable (outerIntegrandM G L γ δ base roots tt layer hS amp frq route hclk hmom (HkMy y) z) μ)
    (hsm : ∀ y ∈ classU Us p kind A us, Summable (fun z : GenDecoration G d roots 0 =>
      (splicedEpsilon G hinges z.1 : ℂ) * Zw z *
        ∫ τ, outerIntegrandM G L γ δ base roots tt layer hS amp frq route hclk hmom (HkMy y) z τ ∂μ)) :
    ∑ y ∈ classU Us p kind A us,
        outerValMμ G L γ δ base roots tt layer hinges Zw hS μ amp frq route hclk hmom (HkMy y) =
      outerValMμ G L γ δ base roots tt layer hinges Zw hS μ amp frq route hclk hmom
        (fun j lam t k => ∑ x ∈ canonFinsetK p kind (Us.st A j) (Us.reg us j), gk j lam t k x) := by
  unfold outerValMμ
  refine sum_outer_core _ μ _ (fun z => (splicedEpsilon G hinges z.1 : ℂ) * Zw z)
    (splicedTimeDomain G layer tt)
    (fun z τ => phaseProd L γ δ G (cosetDecoration G L base z.1) τ *
      (∏ s, amp s (base + latticePoint L (z.1 (slotNode hS s)))) * routedPhase frq route tt τ)
    (fun y z τ => ∏ j, HkMy y j (modLam frq route j) (fun c => clockOf G tt τ (hclk j c))
        (fun c => base + latticePoint L (z.1 (hmom j c))))
    (fun z τ => ∏ j, ∑ x ∈ canonFinsetK p kind (Us.st A j) (Us.reg us j), gk j (modLam frq route j)
        (fun c => clockOf G tt τ (hclk j c)) (fun c => base + latticePoint L (z.1 (hmom j c))) x)
    (fun z τ => sum_classU_prod hA us _ _ fun y hy j => hfg y hy j _ _ _) hint hsm
-- [end copied]

end Outer

-- [copied] world `Flower/V5W/Foreign.lean` lines 137–174 (`weightedClassFactorization`), with `outerValM` →
-- `outerValMμ` (time measure `μ`, complex `Zw`), stated as a theorem (not through the `Prop`
-- `WeightedClassFactorization`), see COPIED-SHA256SUMS.
/-- **T4 against a time measure**: the τ-class sum of the members' per-mode outer values `outerValMμ`, each with its own
weighted unit kernels `unitRecenteredFW`, is the outer value with the weighted class kernels `twistedRecenteredFW`. -/
theorem weightedClassFactorizationμ {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    {U₀ : J₀ → Finset (GBranch S.tree)} {a₀ b₀ : J₀ → GBranch S.tree} {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)}
    {n₀ : J₀ → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j)) (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j'))
    (hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool} (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = (unitsStart B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) {I : Type*} [Fintype I] (sgn : I → ℂ) {Ξ : Type*} (Wt : I → Ξ → ℂ) {d : ℕ}
    (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (lay : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℂ)
    (hG : G.IsPlain) (μ : Measure (GBranch G.tree → ℝ))
    (amp : I → Ξ → ReplacementSlot G → Mom d → ℂ) (frq : I → Ξ → ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀) (hclk : J₀ → Fin 3 → ClkSrc G)
    (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (gU : J₀ → Mom d → ℂ) (SU : J₀ → Option ℝ)
    (hV : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      V y.1.layered = ∑ i, sgn i * ∑' ξ, Wt i ξ *
        outerValMμ G L γ δ base roots tt lay hinges Zw hG μ (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)))
    (hξ : ∀ i, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun ξ => Wt i ξ *
        outerValMμ G L γ δ base roots tt lay hinges Zw hG μ (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    (hint : ∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ z, Integrable (outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
          (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z) μ)
    (hsm : ∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * Zw z *
          ∫ τ, outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
            (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
              (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ ∂μ)) :
    ∑ LG ∈ T, V LG = ∑ i, sgn i * ∑' ξ, Wt i ξ *
      outerValMμ G L γ δ base roots tt lay hinges Zw hG μ (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => twistedRecenteredFW p (gU j) (SU j) S (a₀ j)
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
        unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3) =
          recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
              ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
            twistedLocalKernelFW p (gU j) (SU j)
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).1
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).2
              L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
    intro y hy j lam t k
    obtain ⟨M, _, hR⟩ := (mem_classU hprime).mp hy
    unfold unitRecenteredFW
    rw [hR.sign_upper j, unitKernelFW_classProd hprime ((mem_classU hprime).mp hy) j]
    rfl
  rw [sum_classU_outerValMμ (Us := unitsSplit B₀) (p := p) (kind := kind)
    (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime (unitsRegion B₀ hdisj₀) G L γ δ base roots tt lay hinges Zw hG
    μ (amp i ξ) (frq i ξ) route hclk hmom _
    (fun j lam t k x => recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
        ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
      twistedLocalKernelFW p (gU j) (SU j) x.1 x.2 L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
        (k 0) (k 1) (k 2) (k 3))
    hfg (hint i ξ) (hsm i ξ)]
  congr 1
  funext j lam t k
  unfold twistedRecenteredFW
  exact (Finset.mul_sum _ _ _).symm
-- [end copied]

end WaveTurbulence.Flower.MkSlots
