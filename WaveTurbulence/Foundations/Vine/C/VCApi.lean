/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCSigma
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModClass

/-! # VINE-C adapter to the VINE-D ENGINE API (PLAN-VINE, fixed 2026-11-06)

The engine consumes, per vine piece,
`Σ_{LG ∈ T} value = Σ_i sign_i · Σ'_ξ W_i ξ · outerValM G … (amp_i ξ) (frq_i ξ) route hclk hmom HkM_i` with
`HkM_i j λ = Cont.twistedRecenteredModC S u_j.upper (canonFinsetK p kind (startState B_j D hS layer hLayer)
(chainStart B_j)) L γ δ (fun q => U.h i q j₁ j₁) base λ` (curried in the three clocks and four momenta).

* `clLocalKernelModC_eq_W`, `twistedRecenteredModC_eq_W`, `clRecenteredLocalKernelModC_eq_W`: V5-CONT's modulated kernels
  are the weighted kernels of VINE-C with the weight `modW λ` (the modulation stands on the other side of the summand).
* `sum_tauClass_vineD_api`: the τ-class sum in exactly the engine's form, from VINE-B♯'s per-member, per-mode
  factorization (with the member's unit kernels) and the summability in the mode `ξ` and the integrability/summability of
  each member's outer integrand (the finite interchanges).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 TTree MeasureTheory

variable {w : ℕ}

/-- V5-CONT's modulated unit kernel is the weighted kernel with the weight `modW λ`. -/
theorem clLocalKernelModC_eq_W {d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    VineEstS5C.Cont.clLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      clLocalKernelW D hG R L γ δ F layer hLayer base (modW lam) t0 t1 t2 e f g h := by
  unfold VineEstS5C.Cont.clLocalKernelModC clLocalKernelW VineEstS5C.Cont.lowModC modW
  congr 1
  exact tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => mul_comm _ _)

/-- V5-CONT's recentered modulated unit kernel (the per-member unit factor) in VINE-C's form. -/
theorem clRecenteredLocalKernelModC_eq_W {d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    VineEstS5C.Cont.clRecenteredLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      recPhase (G.sign a.toNode) L γ δ t0 e f g h *
        clLocalKernelW D hG R L γ δ F layer hLayer base (modW lam) t0 t1 t2 e f g h := by
  unfold VineEstS5C.Cont.clRecenteredLocalKernelModC recPhase
  rw [clLocalKernelModC_eq_W]

/-- V5-CONT's modulated class kernel `twistedRecenteredModC` is VINE-C's `twistedRecenteredW` with `W = modW λ`. -/
theorem twistedRecenteredModC_eq_W {κ : Type*} {d : ℕ} (G : Garden w) (a : GBranch G.tree)
    (Z : Finset (Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family)) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    VineEstS5C.Cont.twistedRecenteredModC G a Z L γ δ F base lam t0 t1 t2 e f g h =
      twistedRecenteredW G a Z L γ δ F base (modW lam) t0 t1 t2 e f g h := by
  unfold VineEstS5C.Cont.twistedRecenteredModC twistedRecenteredW recPhase twistedLocalKernelW
  congr 1
  exact Finset.sum_congr rfl fun x _ => clLocalKernelModC_eq_W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The per-member unit factor of VINE-B♯ in V5-CONT's form, at any region data of the carried unit block and any
layering decoding the member, is VINE-C's `unitRecenteredW` with `W = modW λ`. -/
theorem clRecenteredLocalKernelModC_eq_unit {ι : Type*} {Q : ι → Prop} {d : ℕ} (X : FamilyReconstruction w ι)
    (u : UnitAt X.skeleton X.family Q) (R : CLRegionData X.skeleton u.blk.U u.blk.a u.blk.b)
    (layer : GNode (X.data.forest X.plain) → ℕ) (hL : IsLayering (X.data.garden X.plain) layer)
    (hspec : layeredReconstruction X.data X.plain layer hL = X.layered) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    VineEstS5C.Cont.clRecenteredLocalKernelModC X.data X.plain R L γ δ F layer hL base lam t0 t1 t2 e f g h =
      unitRecenteredW X u L γ δ F base (modW lam) t0 t1 t2 e f g h := by
  rw [clRecenteredLocalKernelModC_eq_W]
  exact unitRecenteredW_eq_of_data X u R layer hL hspec L γ δ F base (modW lam) t0 t1 t2 e f g h

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

/-- **The τ-class sum in the form of the VINE-D ENGINE API.**  `hV`: VINE-B♯ at every class member `y` (after the mode
expansion of the outer slots), with the member's unit factors `K̃^{U_j,(λ)}_{(y)}`; `hξ`: summability in the mode;
`hint`, `hsm`: integrability/summability of each member's outer integrand.  Conclusion: the engine's form, with the
unit factors `Cont.twistedRecenteredModC S (a₀ j) (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer)
(chainStart (B₀ j))) L γ δ (F i j) base λ`. -/
theorem sum_tauClass_vineD_api {J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    {U₀ : J₀ → Finset (GBranch S.tree)} {a₀ b₀ : J₀ → GBranch S.tree} {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)}
    {n₀ : J₀ → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j)) (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j'))
    (hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool} (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = (unitsStart B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) {I : Type*} [Fintype I] (sgn : I → ℂ) {Ξ : Type*} (Wt : I → Ξ → ℂ) {d : ℕ}
    (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (lay : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℝ)
    (hG : G.IsPlain) (amp : I → Ξ → ReplacementSlot G → Mom d → ℂ) (frq : I → Ξ → ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀) (hclk : J₀ → Fin 3 → ClkSrc G)
    (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (hV : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      V y.1.layered = ∑ i, sgn i * ∑' ξ, Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3)))
    (hξ : ∀ i, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun ξ => Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3))))
    (hint : ∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ z, Integrable (outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
          (k 0) (k 1) (k 2) (k 3)) z))
    (hsm : ∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
          ∫ τ, outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
            (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
              (k 0) (k 1) (k 2) (k 3)) z τ)) :
    ∑ LG ∈ T, V LG = ∑ i, sgn i * ∑' ξ, Wt i ξ *
      outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => VineEstS5C.Cont.twistedRecenteredModC S (a₀ j)
          (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
          L γ δ (F i j) base lam (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) := by
  rw [sum_layered_eq_sum_classU (Us := unitsSplit B₀) (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime
    (unitsRegion B₀ hdisj₀) T hT V, Finset.sum_congr rfl hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (hξ i)]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_classU_outerValM_kernel (Us := unitsSplit B₀) (p := p) (kind := kind)
    (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime (unitsRegion B₀ hdisj₀) G L γ δ base roots tt lay hinges Zw hG (amp i ξ)
    (frq i ξ) route hclk hmom (F i) (hint i ξ) (hsm i ξ)]
  congr 1
  funext j lam t k
  exact (twistedRecenteredModC_eq_W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

end WaveTurbulence.VineC
