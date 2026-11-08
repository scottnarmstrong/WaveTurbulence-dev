/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Statements
public import WaveTurbulence.Foundations.Flower.V5WA.Instance
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Mono
public import WaveTurbulence.Foundations.Vine.DegenVine.CharMix
public import WaveTurbulence.Foundations.SumintPar.SourceKernelInterpolated
public import WaveTurbulence.Foundations.Spine.LeafwiseLayerInputs
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Mix

/-! # V5W-B-WORLD: the bound restricted to a class of top filters, and its halves

`V5FrontierClassBoundOnAt Sok P` is V5W-0's `V5FrontierClassBoundAt P` (text copied from `Flower/V5W/Statements.lean`, see
`COPIED-SHA256SUMS`) with the extra premise `Sok S` on the top filter `S`.  `V5FrontierClassBoundAt P` follows from the
`S = none` half and the `S ≠ none` half (`v5FrontierClassBoundAt_of_halves`); both halves are monotone in the large
constants, so the gate `V5FrontierClassBound` follows from the two prefix forms (`v5FrontierClassBound_of_halves`).
The `S = none` half is V5W-B's (`Flower/V5WB/Final.lean`); the `S ≠ none` half (the region-top stem filter, supplement
Lemma 9.3) is V5W-T's.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence.Flower.V5W
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

/-- **The bound on a class of top filters** (`V5FrontierClassBoundAt` with the premise `Sok S`). -/
def V5FrontierClassBoundOnAt (Sok : Option ℝ → Prop) (P : WTParams) : Prop :=
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
    ∀ (S : Option ℝ), Sok S → (∀ s, S = some s → 0 < s) →
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

/-- **The two halves give the bound.** -/
theorem v5FrontierClassBoundAt_of_halves (P : WTParams) (hN : V5FrontierClassBoundOnAt (· = none) P)
    (hS : V5FrontierClassBoundOnAt (· ≠ none) P) : V5FrontierClassBoundAt P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hcl centre wBar lam g cψ
    hc hgp hre S hSpos hrow
  by_cases hS0 : S = none
  · exact hN hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hcl centre wBar lam g cψ hc hgp hre S
      hS0 hSpos hrow
  · exact hS hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hcl centre wBar lam g cψ hc hgp hre S
      hS0 hSpos hrow

/-- Each restricted bound is monotone in the large constants (the proof of STAGE1W-VINE's `v5FrontierClassBoundAt_mono`). -/
theorem v5FrontierClassBoundOnAt_mono (Sok : Option ℝ → Prop) : LargeConstantMonotone (V5FrontierClassBoundOnAt Sok) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hcl centre wBar lam g cψ
    hc hgp hre S hSok hS hrow
  have hN := vineEstHalfMK_N P c₁ c₂ (p + 1)
  have key := @h p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay
    (by rw [← hN]; exact hord) (by have := vineEstHalfMK_N P c₁ c₂ 1; rw [← this]; exact hcl) centre wBar lam g cψ
    hc hgp hre S hSok hS hrow
  refine le_trans key (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hL0 : 0 ≤ P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) :=
    Real.rpow_nonneg (by linarith) _
  have hleaf := WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG R layer hLayer hB₀
  have hs : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hc0 : 0 ≤ P.C₁ * Real.sqrt P.δ := mul_nonneg (by linarith) hs
  have hcc : P.C₁ * Real.sqrt P.δ ≤ c₁ * Real.sqrt P.δ := mul_le_mul_of_nonneg_right h₁ hs
  have hpow := pow_le_pow_left₀ hc0 hcc (clLocalOrder2 RD hG R)
  have h1 : 0 ≤ (1 + |lam|) ^ (6 * P.η ^ 6) := Real.rpow_nonneg (by positivity) _
  show (1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _) ≤
    (1 + |lam|) ^ (6 * P.η ^ 6) * ((c₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _)
  gcongr

/-- **The gate from its two halves** (the `S ≠ none` half is V5W-T's). -/
theorem v5FrontierClassBound_of_halves (hN : WTPrefix (V5FrontierClassBoundOnAt (· = none)))
    (hS : WTPrefix (V5FrontierClassBoundOnAt (· ≠ none))) : V5FrontierClassBound :=
  Flower.V5WA.wtPrefix_mono (prefix_and hN hS (v5FrontierClassBoundOnAt_mono _) (v5FrontierClassBoundOnAt_mono _))
    fun P h => v5FrontierClassBoundAt_of_halves P h.1 h.2

end WaveTurbulence.Flower.V5WB
