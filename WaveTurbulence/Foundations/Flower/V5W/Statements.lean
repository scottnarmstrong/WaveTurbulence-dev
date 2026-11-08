/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Defs
public import WaveTurbulence.Foundations.Vine.DegenVine.CharMix
public import WaveTurbulence.Foundations.SumintPar.SourceKernelInterpolated
public import WaveTurbulence.Foundations.Spine.LeafwiseLayerInputs
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Mix

/-! # V5W-0: the statements of the weighted vine estimate (S-V5W SCOPE §2.2–§2.4)

Ported by source from the S-V5W probe (sha256 `efdab782…f05f6`, see `COPIED-SHA256SUMS`), §5–§7.

* `V5FrontierClassBoundAt` / `V5FrontierClassBound`: the bound (V5W-B's target; stated here so that O3′ can stage it).
* **T4** `WeightedClassFactorization` (with its key lemma `UnitKernelFWForeign`): the weighted
  `VineC.sum_tauClass_vineD_api`.
* **T5** `WeightedClassContinuity`: the weighted `Cont.twistedRecenteredModC_continuousOn`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB WaveTurbulence.VineC WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W
open scoped ENNReal FourierTransform
open Set
open VineEstS5C.P4.Final LGSpine Cut2A

/-! ## §5 (B) The bound -/

/-- **(B) `V5FrontierClassBoundAt`** — the minimal weighted vine estimate (supplement Lemma 5.3, V5 form): verbatim
`VineEstCanonLayerHalfMK` except for the weight binders `g cψ S` with their premises (`g` real and `GPresented`) and
the class kernel `twistedRecenteredFW p (g a.1.1) S … (modW lam)`; mass `cψ ^ (9|U| + 4 n₍₂₎) · topFilterMass`. -/
def V5FrontierClassBoundAt (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (g : Fin w → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
      (∀ j x, (g j x).im = 0) →
    ∀ (S : Option ℝ), (∀ s, S = some s → 0 < s) →
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecenteredFW p (g a.1.1) S G a
        (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar (modW lam)
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal (cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * topFilterMass) *
      ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

/-- **`V5FrontierClassBound`** (gate form, frozen `WTPrefix`). -/
def V5FrontierClassBound : Prop := WTPrefix V5FrontierClassBoundAt

/-! ## §6 T4: the weighted class factorization (weighted `VineC.sum_tauClass_vineD_api`) -/

/-- **T4.** The τ-class sum of the members' per-mode outer values, each with its OWN weighted unit kernels, equals the
outer value with the weighted class kernels `twistedRecenteredFW` of the units. Unit `j` lies in one tree and carries
`gU j`, `SU j`. Hypotheses as in main's `sum_tauClass_vineD_api` (VINE-B♯ factorization `hV` is O3′'s T3). -/
def WeightedClassFactorization : Prop :=
  ∀ {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    {U₀ : J₀ → Finset (GBranch S.tree)} {a₀ b₀ : J₀ → GBranch S.tree} {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)}
    {n₀ : J₀ → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j)) (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j'))
    (_hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool} (T : Finset (LayeredGarden w))
    (_hT : (T : Set (LayeredGarden w)) = (unitsStart B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) {I : Type*} [Fintype I] (sgn : I → ℂ) {Ξ : Type*} (Wt : I → Ξ → ℂ) {d : ℕ}
    (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (lay : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℝ)
    (hG : G.IsPlain) (amp : I → Ξ → ReplacementSlot G → Mom d → ℂ) (frq : I → Ξ → ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀) (hclk : J₀ → Fin 3 → ClkSrc G)
    (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (gU : J₀ → Mom d → ℂ) (SU : J₀ → Option ℝ),
    (∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      V y.1.layered = ∑ i, sgn i * ∑' ξ, Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) →
    (∀ i, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun ξ => Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)))) →
    (∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ z, Integrable (outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
          (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z)) →
    (∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
          ∫ τ, outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
            (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
              (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ)) →
    ∑ LG ∈ T, V LG = ∑ i, sgn i * ∑' ξ, Wt i ξ *
      outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => twistedRecenteredFW p (gU j) (SU j) S (a₀ j)
          (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
          L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))

/-- T4's key lemma (weighted `VineC.unitKernelW_foreign`): an operation at a member outside the unit leaves the unit's
weighted kernel unchanged (rows rigid, core layers preserved, region darts untouched). -/
def UnitKernelFWForeign : Prop :=
  ∀ {w : ℕ} {ι : Type*} {Q : ι → Prop} {p : ℕ} {kind : Bool} {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (S : Option ℝ)
    (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q) {i : ι}
    (_hi : ¬ Q i) (op : FamilyOperation (p := p) (kind := kind) X i)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d),
    unitKernelFW pw g S op.output (u.nextA X i op.choice) L γ δ F base W t0 t1 t2 e f g' h =
      unitKernelFW pw g S X u L γ δ F base W t0 t1 t2 e f g' h

/-! ## §7 T5: continuity of the weighted class kernel (weighted `twistedRecenteredModC_continuousOn`) -/

/-- **T5.** Hypotheses of main's `twistedRecenteredModC_continuousOn` plus INC-TOP's gate at `P` and the weight data;
conclusion: continuity of the pinned class kernel in the three hinge times on the output cube, for every output. -/
def WeightedClassContinuity : Prop :=
  ∀ {w : ℕ} {kind : Bool} {P : WTParams} (lam : ℝ)
    (_hgate : CoherentGateH P) (_hinc : IncoherentGateH P) (_htop : TopIncoherentDecayAtR P)
    (_hd : 1 ≤ P.d) (_hη0 : 0 < P.η) (_hη6 : 6 * P.η ^ 6 ≤ P.η) (_hη2 : P.η ≤ 1 / 2)
    (_hC : 1 ≤ P.C₁) (_hδ : 0 < P.δ) (_hL : 1 ≤ P.L) (_hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (_hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (_hB : ProfileBound P h Bh p) (_hBpos : ∀ r ≤ p, 0 < Bh r)
    {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (_hlay : ∀ x, layer x ≤ p) (_hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (g : Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → GPresented (32 * P.d) g cψ → (∀ x, (g x).im = 0) →
    ∀ (S : Option ℝ), (∀ s, S = some s → 0 < s) →
    RowCoherent hM9 B RD hG layer hLayer
      (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    ∀ E ∈ Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
        P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => twistedRecenteredFW p g S G a
          (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)) P.L P.γ P.δ h wBar (modW lam)
          (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3))
        (VineEstS3.cubeSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R)
          centre wBar).qOut)

end WaveTurbulence.Flower.V5W
