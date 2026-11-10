/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WT.Engine
public import WaveTurbulence.Foundations.Flower.V5WB.K.FlatBound
public import WaveTurbulence.Foundations.Flower.V5WB.W2.FinalS
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core2

/-! # V5W-T T5′: the weighted flat bound with an output-dependent multiplier

Copies by source of V5W-B-WORLD's `Flower/V5WB/K/Defs.lean` (`VineFlatC2MX`, `VineFlatHalfMX`), `K/FlatEstimate.lean`,
`K/FlatHalf.lean`, `K/FlatPrefix.lean` (sha256 in `COPIED-SHA256SUMS`).  Edits: suffix `Out`; the multiplier's
`EnginePullback` is an `EnginePullbackOut`; the two certificate consumers `W2.habsW`/`W2.termBoundW ∘ termCertW_mul` are
`habsWOut`/`termBoundWOut` (T3) with the extra engine input `hdbO : SumintMixParDoubledOutAt 6561 Pe`, which the prefix
assembly supplies next to main's `hdb` through `prefixA_and` (the `WTPrefixA` analogue of `LGSpine.prefix_and`) of
main's `sumintMixParDoubled` and T2's `sumintMixParDoubledOut`.  Everything else (`wpF_flatBMX`, the certificate
`UniformTermCertTargetKS`, the gates) is V5W-B-WORLD's / main's, by import.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB

/-- **Conjunction of two `WTPrefixA` statements** (copy of `LGSpine.prefix_and` with the constant `A`). -/
theorem prefixA_and {Q₁ Q₂ : ℝ → WTParams → Prop} (h₁ : WTPrefixA Q₁) (h₂ : WTPrefixA Q₂)
    (hm₁ : ∀ A, LGSpine.LargeConstantMonotone (Q₁ A)) (hm₂ : ∀ A, LGSpine.LargeConstantMonotone (Q₂ A)) :
    WTPrefixA (fun A P => Q₁ A P ∧ Q₂ A P) := by
  intro d hd γ hγ
  obtain ⟨ηA, hηA, hA⟩ := h₁ d hd γ hγ
  obtain ⟨ηB, hηB, hB⟩ := h₂ d hd γ hγ
  refine ⟨min ηA ηB, lt_min hηA hηB, ?_⟩
  intro η hη A hA1 φin hφin τ hτ φ hsol
  obtain ⟨CA, hCA, νA, hνA, hA⟩ := hA η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ A hA1 φin hφin τ hτ φ hsol
  obtain ⟨CB, hCB, νB, hνB, hB⟩ := hB η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩ A hA1 φin hφin τ hτ φ hsol
  refine ⟨max CA CB, hCA.trans (le_max_left _ _), min νA νB, lt_min hνA hνB, ?_⟩
  intro ν hν
  obtain ⟨δA, hδA, hA⟩ := hA ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δB, hδB, hB⟩ := hB ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨min δA δB, lt_min hδA hδB, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂A, hC₂A, LA, hLA, hA⟩ := hA δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD htime
  obtain ⟨C₂B, hC₂B, LB, hLB, hB⟩ := hB δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD htime
  refine ⟨max C₂A C₂B, hC₂A.trans (le_max_left _ _), max LA LB, hLA.trans (le_max_left _ _), ?_⟩
  intro L hL
  constructor
  · exact hm₁ A _ _ _ hCA hC₂A hδ.1 (hLA.trans ((le_max_left _ _).trans hL)) (le_max_left _ _) (le_max_left _ _)
      (hA L ((le_max_left _ _).trans hL))
  · exact hm₂ A _ _ _ hCB hC₂B hδ.1 (hLB.trans ((le_max_right _ _).trans hL)) (le_max_right _ _) (le_max_right _ _)
      (hB L ((le_max_right _ _).trans hL))

section Statements
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine

/-- Main's `VineSpaceK.VineFlatC2MX` for every selector, with the selector's top layer `p` and presentation
(`rowSel.weighted = true →`; vacuous for an unweighted selector). -/
def VineFlatC2MXOut (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D →
    (rowSel.weighted = true → rowSel.p = p ∧ Flower.Stage1W.GPresented (32 * P.d) (rowSel.g P.d) rowSel.cψ) →
    ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (mass : ℝ), 0 ≤ mass →
    EnginePullbackOut (Lvl.top B).region P.L wBar m mass →
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (flatFnRMX (p := p) (kind := kind) B RD hG layer hLayer m lam (G.sign a.toNode)
        (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode)) ≤
    ENNReal.ofReal mass * ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card))

/-- Main's `VineSpaceK.VineFlatHalfMX` for every selector, with the same selector hypothesis. -/
def VineFlatHalfMXOut (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D →
    (rowSel.weighted = true → rowSel.p = p ∧ Flower.Stage1W.GPresented (32 * P.d) (rowSel.g P.d) rowSel.cψ) →
    ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (mass : ℝ), 0 ≤ mass →
    EnginePullbackOut (Lvl.top B).region P.L wBar m mass →
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (flatFnRMX (p := p) (kind := kind) B RD hG layer hLayer m lam (G.sign a.toNode)
        (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode)) ≤
    ENNReal.ofReal mass * ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)))


end Statements

section Estimate
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal

open VineEstS5C.P4.Final

/-- `VineFlatC2MXOut` with `0 < B₀` (the form the certificate `UniformTermCertAtK` binds, R105 F8). -/
def VineFlatC2MXPosOut (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D →
    (rowSel.weighted = true → rowSel.p = p ∧ Flower.Stage1W.GPresented (32 * P.d) (rowSel.g P.d) rowSel.cψ) →
    ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 < B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (mass : ℝ), 0 ≤ mass →
    EnginePullbackOut (Lvl.top B).region P.L wBar m mass →
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (flatFnRMX (p := p) (kind := kind) B RD hG layer hLayer m lam (G.sign a.toNode)
        (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode)) ≤
    ENNReal.ofReal mass * ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card))

theorem vineFlatC2MXPosOut_core (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKS 6561 Pe Km Kr Kb)
    (htop : Flower.Stage1W.TopIncoherentDecayAt Pe) (hdbO : SumintMixParDoubledOutAt 6561 Pe)
    (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineFlatC2MXPosOut ({Pe with C₁ := C₁} : WTParams) := by
  intro p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh
  have hL1 : 1 ≤ Pe.L := by linarith
  have hB : ProfileBound Pe (truncF p h) (fun _ => B₀) p := fun r hr => ⟨hB₀.le, by rw [truncF_eq h r hr]; exact hh r hr⟩
  have E : GateEnv Pe (kparOf Pe.L Pe.γ Pe.δ (truncF p h) wBar) p (fun _ => B₀) :=
    ⟨hgate, hB, hp, rfl, by linarith, by linarith, hc0⟩
  have hcohE : RowCoherent hM9 B RD hG layer hLayer
      (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.δ (truncF p h) p := hcoh
  have hN : ∀ k, Pe.N k = ({Pe with C₁ := C₁} : WTParams).N k := fun k => (N_largeConstants Pe C₁ Pe.C₂ k).symm
  have hordE : (RD.garden hG).order ≤ Pe.N (p + 1) ^ 4 := by rw [hN]; exact hord
  have hl1E : clLocalOrder1 R ≤ Pe.N 1 ^ 4 := by rw [hN]; exact hl1
  obtain ⟨β', hcert, hβ'⟩ := hUC (truncF p h) B₀ wBar hB₀ E hinc (fun hw => ⟨(hsp hw).1, (hsp hw).2, htop⟩) hprime hM9 B RD hG layer hLayer kind hcan hlay hordE hl1E centre lam hR hcohE
  have hKb0 : 0 < Kb := by linarith only [hKb]
  refine le_trans (wpF_flatBMX (C₂ := Pe.C₂ / Kb) (Λ := mass * (1 + |lam|) ^ (6 * Pe.η ^ 6)) (Ns := engNs Pe.η Pe.C₁ Km Kr) (δ := Pe.δ) (C₁ := C₁)
    (Lp := Kb ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card *
      Pe.L ^ (-(Pe.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        Pe.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7))
    (lf := regionLeafSize RD hG R layer hLayer (fun _ => B₀)) (p := p) (kind := kind) B RD hG layer hLayer (hprime' := hprime) hM9 hR E hordE m lam (G.sign a.toNode)
    (G.sign a.toNode) (fun c => ((qOutOf RD hG layer a b R c : ℕ) : ℝ))
    (Bx := WaveTurbulence.VineEstS3.Eng.outBox
      (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
    (fun tt ht c => ⟨(ht.1 c).1, (ht.1 c).2⟩)
    (K := WaveTurbulence.VineEstS3.Eng.outSet
      (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.η)
    (WaveTurbulence.VineEstS3.Eng.countable_outSet _ _ _ _) (fun tt ht => ⟨(ht.1 0).1, (ht.1 0).2⟩)
    (fun ψ hψ tt htt E' hE' => habsWOut (P := Pe) (A := 6561) B hG _ rfl (Lvl.top B) _ rfl (modPsi b lam ψ)
        (hcert ψ hψ) m hpull tt htt E' hE')
    (D := Pe.D) hp.le ?_ ?_ ?_ ?_ ?_ hC₁ ((le_div_iff₀ hKb0).2 hC₂)) (le_of_eq ?_)
  · intro ψ hψ
    exact (termBoundWOut (P := Pe) (A := 6561) B hG hdbO _ rfl rfl rfl (Lvl.top B) (G.sign a.toNode) (G.sign a.toNode)
      rfl rfl (modPsi b lam ψ) (hcert ψ hψ) m hpull).trans (by
        calc
          _ = ENNReal.ofReal mass * (‖(coupling Pe.d Pe.L Pe.γ Pe.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ * β') := by
            ac_rfl
          _ ≤ ENNReal.ofReal mass * _ := mul_le_mul' (le_refl (ENNReal.ofReal mass)) hβ'
          _ = _ := by rw [← ENNReal.ofReal_mul hmass]; congr 1; ring)
  · exact mul_nonneg hmass (Real.rpow_nonneg (by positivity) _)
  · have h1 : 0 < Km := by linarith
    have h2 : 0 < Kr := by linarith
    have h3 : 0 < Pe.C₁ := by linarith
    unfold engNs
    positivity
  · exact mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  · exact regionLeafSize_const_nonneg RD hG R layer hLayer hB₀.le
  · rw [← ENNReal.ofReal_mul hmass]
    congr 1
    rw [div_pow]
    field_simp

/-- **F8 limit argument for the flat form** (copy of `vineEstCanonLayerC2MK_of_pos`): `0 ≤ B₀` from `0 < B₀`. -/
theorem vineFlatC2MXOut_of_pos (P : WTParams) (H : VineFlatC2MXPosOut P) : VineFlatC2MXOut P := by
  intro p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass
    hmass hpull hcoh
  have e : ∀ a b c d e0 : ℝ, mass * (a * (b * c * e0 * d)) = (mass * (a * (b * c * d))) * e0 :=
    fun a b c d e0 => by ring
  rw [← ENNReal.ofReal_mul hmass]
  conv_rhs => rw [e]
  refine le_regionLeafSize_of_forall_pos RD hG layer hLayer (fun _ => B₀) _ (fun ε hε => ?_)
  have key := H hp hsp h (B₀ + ε) (by linarith) (fun r hr => (hh r hr).trans (ENNReal.ofReal_le_ofReal (by linarith)))
    hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh
  rw [← ENNReal.ofReal_mul hmass] at key
  exact le_of_le_of_eq key (congrArg ENNReal.ofReal (e _ _ _ _ _))

theorem vineFlatC2MXOut_core (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKS 6561 Pe Km Kr Kb)
    (htop : Flower.Stage1W.TopIncoherentDecayAt Pe) (hdbO : SumintMixParDoubledOutAt 6561 Pe)
    (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineFlatC2MXOut ({Pe with C₁ := C₁} : WTParams) :=
  vineFlatC2MXOut_of_pos _ (vineFlatC2MXPosOut_core Pe C₁ Km Kr Kb hKm hKr hKb hR hgate hinc hUC htop hdbO hc0 hη0 hη1 hL hC₁ hC₂)


omit rowSel in
/-- **R54 (ii) from (i), modulated, for every selector** (the selector is bound after the record). -/
theorem vineFlatHalfMXOut_of_C2MX (H : WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatC2MXOut P) :
    WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXOut P := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, max L₀ (C₂ ^ (2 / η ^ 2)), le_max_of_le_left hL₀, fun L hL => ?_⟩
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLC : C₂ ^ (2 / η ^ 2) ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  intro u _I
  have key : VineFlatC2MXOut ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ := H4 L hLL₀
  intro p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh
  refine (key hp hsp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have hδ0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  exact half_of_C2_real (pow_nonneg (mul_nonneg (by linarith) hδ0) _)
    (regionLeafSize_const_nonneg RD hG R layer hLayer hB₀) hLpos (C2_pow_le _ hη.1 hC₂ hLC)


end Estimate

section Prefix
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar
  VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final

omit rowSel in
/-- **The weighted flat estimate for every selector, on the prefix** (V5W-A's `vineFlatC2MX_of_uniformCert` with the
selector certificate `UniformTermCertTargetKS` and INC-TOP's gate). -/
theorem vineFlatC2MXOut_of_uniformCert (hU : UniformTermCertTargetKS) (hG : LeafwiseCoherentApproximationGate)
    (hI : LeafwiseIncoherentDecayGate) (hR : RealityAll) (hT : Flower.Stage1W.TopIncoherentDecayGateR) :
    WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatC2MXOut P := by
  have hI : WTPrefix fun P => LeafwiseIncoherentDecayAt P ∧ Flower.Stage1W.TopIncoherentDecayAtR P :=
    prefix_and hI hT leafwiseIncoherentDecay_largeConstantMonotone
      Flower.Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone
  intro d hd γ hγ
  obtain ⟨ηU, hηU, hUa⟩ := hU d hd γ hγ
  obtain ⟨ηS, hηS, hSa⟩ := prefixA_and (Q₁ := SumintMixParDoubledAt) (Q₂ := SumintMixParDoubledOutAt)
    sumintMixParDoubled sumintMixParDoubledOut sumintMixPar_mono sumintMixParOut_mono d hd γ hγ
  obtain ⟨ηG, hηG, hGa⟩ := hG d hd γ hγ
  obtain ⟨ηI, hηI, hIa⟩ := hI d hd γ hγ
  refine ⟨min (min ηU (min ηS (min ηG ηI))) (1 / 5), lt_min (lt_min hηU (lt_min hηS (lt_min hηG hηI))) (by norm_num), ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  have hη0 : 0 < η := hη.1
  have hm : η ≤ min ηU (min ηS (min ηG ηI)) := hη.2.trans (min_le_left _ _)
  have hη5 : η ≤ 1 / 5 := hη.2.trans (min_le_right _ _)
  have hηU' : η ∈ Ioc 0 ηU := ⟨hη0, hm.trans (min_le_left _ _)⟩
  have hηS' : η ∈ Ioc 0 ηS := ⟨hη0, hm.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hηG' : η ∈ Ioc 0 ηG := ⟨hη0, hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hηI' : η ∈ Ioc 0 ηI := ⟨hη0, hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨CS, hCS, νS, hνS, hSb⟩ := hSa η hηS' 6561 (by norm_num) φin hφin τ hτ φ hsol
  obtain ⟨CG, hCG, νG, hνG, hGb⟩ := hGa η hηG' φin hφin τ hτ φ hsol
  obtain ⟨CI, hCI, νI, hνI, hIb⟩ := hIa η hηI' φin hφin τ hτ φ hsol
  set c₀ : ℝ := max (max CS CG) CI with hc₀d
  have hc₀ : 1 ≤ c₀ := hCS.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hCSc : CS ≤ c₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hCGc : CG ≤ c₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hCIc : CI ≤ c₀ := le_max_right _ _
  obtain ⟨Km, Kr, hKm, hKr, hUb⟩ := hUa η hηU' φin hφin τ hτ φ hsol c₀ hc₀
  set C₁ : ℝ := max 1 ((Eng.ccη η + 1).toReal * countKc * engNs η c₀ Km Kr) with hC₁d
  refine ⟨C₁, le_max_left _ _, min νS (min νG νI), lt_min hνS (lt_min hνG hνI), ?_⟩
  intro ν hν
  have hνS' : ν ∈ Ioc 0 νS := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hνG' : ν ∈ Ioc 0 νG := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hνI' : ν ∈ Ioc 0 νI := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨δS, hδS, hSc⟩ := hSb ν hνS'
  obtain ⟨δG, hδG, hGc⟩ := hGb ν hνG'
  obtain ⟨δI, hδI, hIc⟩ := hIb ν hνI'
  refine ⟨min δS (min δG δI), lt_min hδS (lt_min hδG hδI), ?_⟩
  intro δ hδ D hD htime
  have hδS' : δ ∈ Ioc 0 δS := ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩
  have hδG' : δ ∈ Ioc 0 δG := ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hδI' : δ ∈ Ioc 0 δI := ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨Kb, hKb, hUb'⟩ := hUb ν δ D hδ.1 htime
  obtain ⟨C₂S, hC₂S, LS, hLS, hSd⟩ := hSc δ hδS' D hD htime
  obtain ⟨C₂G, hC₂G, LG, hLG, hGd⟩ := hGc δ hδG' D hD htime
  obtain ⟨C₂I, hC₂I, LI, hLI, hId⟩ := hIc δ hδI' D hD htime
  refine ⟨max (max C₂S (max C₂G C₂I)) (countKp D * Kb), hC₂S.trans ((le_max_left _ _).trans (le_max_left _ _)), max LS (max LG LI),
    hLS.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLS' : LS ≤ L := (le_max_left _ _).trans hL
  have hLG' : LG ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLI' : LI ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hL2 : 2 ≤ L := hLS.trans hLS'
  set C₂ : ℝ := max (max C₂S (max C₂G C₂I)) (countKp D * Kb) with hC₂d
  have hC₂S' : C₂S ≤ C₂ := (le_max_left _ _).trans (le_max_left _ _)
  have hC₂G' : C₂G ≤ C₂ := (le_max_of_le_right (le_max_left _ _)).trans (le_max_left _ _)
  have hC₂I' : C₂I ≤ C₂ := (le_max_of_le_right (le_max_right _ _)).trans (le_max_left _ _)
  have hC₂K : (countKp D : ℝ) * Kb ≤ C₂ := le_max_right _ _
  let PS : WTParams := ⟨d, γ, η, φin, τ, φ, CS, ν, δ, D, C₂S, L⟩
  let PG : WTParams := ⟨d, γ, η, φin, τ, φ, CG, ν, δ, D, C₂G, L⟩
  let PI : WTParams := ⟨d, γ, η, φin, τ, φ, CI, ν, δ, D, C₂I, L⟩
  let Pe : WTParams := ⟨d, γ, η, φin, τ, φ, c₀, ν, δ, D, C₂, L⟩
  have hdb : SumintMixParDoubledAt 6561 Pe :=
    sumintMixPar_mono 6561 PS c₀ C₂ hCS hC₂S hδ.1 hL2 hCSc hC₂S' (hSd L hLS').1
  have hdbO : SumintMixParDoubledOutAt 6561 Pe :=
    sumintMixParOut_mono 6561 PS c₀ C₂ hCS hC₂S hδ.1 hL2 hCSc hC₂S' (hSd L hLS').2
  have hgate : CoherentGateH Pe :=
    coherentGateH_of (leafwiseCoherentAt_largeConstantMonotone PG c₀ C₂ hCG hC₂G hδ.1 (hLG.trans hLG') hCGc hC₂G'
      (hGd L hLG'))
  have hIT := (leafwiseIncoherentDecay_largeConstantMonotone.and
    Flower.Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone) PI c₀ C₂ hCI hC₂I hδ.1 (hLI.trans hLI') hCIc hC₂I'
      (hId L hLI')
  have hinc : IncoherentGateH Pe := incoherentGateH_of hIT.1
  have htop : Flower.Stage1W.TopIncoherentDecayAt Pe := Flower.Stage1W.topIncoherentDecayAt_of_R _ hIT.2
  have hη6 : 6 * η ^ 6 ≤ η := by
    have h5 : η ^ 5 ≤ (1 / 5 : ℝ) ^ 5 := pow_le_pow_left₀ hη0.le hη5 5
    calc 6 * η ^ 6 = 6 * η ^ 5 * η := by ring
      _ ≤ 6 * (1 / 5) ^ 5 * η := by gcongr
      _ ≤ η := by nlinarith
  have hAmb : AmbP 6561 Pe :=
    ⟨hdb, by show 0 < L; linarith, hη0, by show η ≤ 1 / 2; linarith, by show η < 1 / 4; linarith,
      by show 0 ≤ c₀; linarith, hδ.1, by show 1 ≤ d; omega, by show 6 * η ^ 6 ≤ 1 - η; linarith, hη6,
      by show 3 * η ≤ 1; linarith⟩
  intro u _I
  have hUC : UniformTermCertAtKS 6561 Pe Km Kr Kb := hUb' C₂ L hL2 hAmb
  have key : VineFlatC2MXOut ({Pe with C₁ := C₁} : WTParams) := vineFlatC2MXOut_core Pe C₁ Km Kr Kb hKm hKr hKb hR hgate
    hinc hUC htop hdbO hc₀ hη0 (by show η ≤ 1 / 2; linarith) hL2 (le_max_right _ _) hC₂K
  exact @key

omit rowSel in
/-- **`WTPrefix VineFlatHalfMX`** for every selector, from the same inputs. -/
theorem vineFlatHalfMXOut_of_uniformCert (hU : UniformTermCertTargetKS) (hG : LeafwiseCoherentApproximationGate)
    (hI : LeafwiseIncoherentDecayGate) (hR : RealityAll) (hT : Flower.Stage1W.TopIncoherentDecayGateR) :
    WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXOut P :=
  vineFlatHalfMXOut_of_C2MX (vineFlatC2MXOut_of_uniformCert hU hG hI hR hT)


end Prefix

end WaveTurbulence.Flower.V5WT
