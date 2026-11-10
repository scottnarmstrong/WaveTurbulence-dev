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

/-! ## §7 T5: continuity of the weighted class kernel (weighted `twistedRecenteredModC_continuousOn`) -/

end WaveTurbulence.Flower.V5W
