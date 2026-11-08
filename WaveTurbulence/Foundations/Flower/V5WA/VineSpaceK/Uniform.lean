module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Certificate
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.UniformIface

/-! R78/R82 uniform certificates for structurally realized spatial mixtures. -/

@[expose] public section
namespace WaveTurbulence.VineSpaceK
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open Set

open VineEstS5C.P4.Final

def UniformTermCertMixAt (A : ℝ) (Pe : WTParams) (Km Kr Kb : ℝ) : Prop :=
  ∀ {p : ℕ} (h : ℕ → Mom Pe.d → ℝ) (B₀ : ℝ) (wBar : Mom Pe.d), 0 < B₀ →
    ∀ (E : GateEnv Pe (kparOf Pe.L Pe.γ Pe.δ h wBar) p (fun _ => B₀)) (_hinc : IncoherentGateH Pe)
      {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    ∀ (hord : (RD.garden hG).order ≤ Pe.N (p + 1) ^ 4), clLocalOrder1 R ≤ Pe.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom Pe.d) (lam : ℝ) (hR : RealityAll),
    RowCoherent hM9 B RD hG layer hLayer
      (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.δ h p →
    ∃ β' : ℝ≥0∞,
      (∀ (m : (GNode G.tree → Fin Pe.d → ℤ) → ℂ) (mass : ℝ),
        EnginePullback (Lvl.top B).region Pe.L wBar m mass →
        ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer
          (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime) B RD hG layer hLayer E hord))
          (bundleBotFamOf B RD hG layer hLayer hprime hR (botSffOf B RD hG layer hLayer hprime E hord))
          (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
        W2.TermCertW (A := A) B hG (kparOf Pe.L Pe.γ Pe.δ h wBar) (Lvl.top B) (spatialMul m (modPsi b lam ψ))
          (openTop (WaveTurbulence.VineEstS3.Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
            (layer (RD.coreBranch hG a).toNode : ℝ))
          (WaveTurbulence.VineEstS3.Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
            Pe.L Pe.γ Pe.η) (ENNReal.ofReal mass * β')) ∧
      ‖(coupling Pe.d Pe.L Pe.γ Pe.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ * β' ≤
        ENNReal.ofReal ((1 + |lam|) ^ (6 * Pe.η ^ 6) * ((engNs Pe.η Pe.C₁ Km Kr * Real.sqrt Pe.δ) ^ clLocalOrder2 RD hG R *
          (Kb ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card *
          Pe.L ^ (-(Pe.η ^ 8 * ((cohmolIndex B RD hG layer +
            (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
            Pe.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7)) *
          regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

/-- The generic ψ certificate lifts without any new W2 analytic estimate.
The only additional input is the explicit lattice Fourier realization. -/
theorem uniformTermCertMixAt_of_uniform (A : ℝ) (Pe : WTParams) (Km Kr Kb : ℝ)
    (H : UniformTermCertAtK A Pe Km Kr Kb) : UniformTermCertMixAt A Pe Km Kr Kb := by
  intro p h B₀ wBar hB₀ E hinc w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre lam hR hcoh
  obtain ⟨β', hc, hb⟩ := H h B₀ wBar hB₀ E hinc hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre lam hR hcoh
  refine ⟨β', ?_, hb⟩
  intro m mass hpull ψ hψ
  exact termCertW_mul B hG _ (Lvl.top B) (modPsi b lam ψ) (hc ψ hψ) m hpull

/-- The unit mixture returns the original R82 certificate target. -/
theorem uniformTermCertAt_of_mix (A : ℝ) (Pe : WTParams) (Km Kr Kb : ℝ)
    (H : UniformTermCertMixAt A Pe Km Kr Kb) : UniformTermCertAtK A Pe Km Kr Kb := by
  intro p h B₀ wBar hB₀ E hinc w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre lam hR hcoh
  obtain ⟨β', hc, hb⟩ := H h B₀ wBar hB₀ E hinc hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre lam hR hcoh
  refine ⟨β', ?_, hb⟩
  intro ψ hψ
  simpa only [spatialMul_one, ENNReal.ofReal_one, one_mul] using
    hc (fun _ => 1) 1 (enginePullback_one (Lvl.top B).region Pe.L wBar) ψ hψ

def UniformTermCertMixTarget : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ φin : SchwartzMap (Mom d) ℝ, (∀ k, 0 ≤ φin k) →
  ∀ τstar : ℝ, 0 < τstar → ∀ φ : ℝ → SchwartzMap (Mom d) ℝ, IsWKESolution φin τstar φ →
  ∀ c0 : ℝ, 1 ≤ c0 →
  ∃ Km Kr : ℝ, 1 ≤ Km ∧ 1 ≤ Kr ∧
  ∀ (ν δ : ℝ) (D : ℕ), 0 < δ → τstar = D * δ →
  ∃ Kb : ℝ, 1 ≤ Kb ∧
  ∀ (C₂ L : ℝ), 2 ≤ L →
    AmbP 6561 (⟨d, γ, η, φin, τstar, φ, c0, ν, δ, D, C₂, L⟩ : WTParams) →
    UniformTermCertMixAt 6561 (⟨d, γ, η, φin, τstar, φ, c0, ν, δ, D, C₂, L⟩ : WTParams) Km Kr Kb

/-- Prefix constants retain exactly the R78 dependency order. -/
theorem uniformTermCertMixTarget_of_uniform (H : UniformTermCertTargetK) : UniformTermCertMixTarget := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, Hη⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τstar hτstar φ hsol c0 hc0
  obtain ⟨Km, Kr, hKm, hKr, HK⟩ := Hη η hη φin hφin τstar hτstar φ hsol c0 hc0
  refine ⟨Km, Kr, hKm, hKr, ?_⟩
  intro ν δ D hδ ht
  obtain ⟨Kb, hKb, HB⟩ := HK ν δ D hδ ht
  exact ⟨Kb, hKb, fun C₂ L hL amb => uniformTermCertMixAt_of_uniform _ _ _ _ _ (HB C₂ L hL amb)⟩

end WaveTurbulence.VineSpaceK
