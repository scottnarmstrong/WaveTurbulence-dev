/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.ClassM
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ModStatement

/-! # V5 FINAL: the interface W2 must deliver (`UniformTermCertTargetK`)

For every configuration of `VineEstCanonLayerC2M` at the ENGINE parameters `Pe` (the statement's parameters with `C₁ := c0`) with a gate
environment, ONE uniform bound `β'` such that every modulated term `modPsi b λ ψ`, `ψ ∈ Lvl.termsB`, carries `TermCertW` with the
engine's own output box/set, and `‖c ζ‖ₑ β' ≤ Λ (Nₛ √δ)^{n₍₂₎} Lp lf`, `Nₛ = engNs η c0 Km Kr` with `Km Kr` fixed before `ν, δ, D, L`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.Final
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open Set

/-- **The uniform per-term certificate at one engine parameter `Pe`** (the content of `UniformTermCertTargetK` below the constants).
Configuration = the binders of `VineEstCanonLayerC2M` (with the gate environment `E` of the profile bound `h`, `Bh = fun _ => B₀`,
and `hR : RealityAll` for the bundle families).  Conclusion: a uniform `β'`, `TermCertW` for every modulated term of
`Lvl.termsB` at the engine's output box and set (R105: with `0 < B₀` and the premise `hcan : CanonicalObject p kind (layeredReconstruction ..)`), and `‖c ζ‖ₑ β' ≤ ofReal (Λ ((Nₛ √δ)^{n₍₂₎} Lp lf))`. -/
def UniformTermCertAtK (A : ℝ) (Pe : WTParams) (Km Kr Kb : ℝ) : Prop :=
  ∀ {p : ℕ} (h : ℕ → Mom Pe.d → ℝ) (B₀ : ℝ) (wBar : Mom Pe.d), 0 < B₀ →
    ∀ (E : GateEnv Pe (kparOf Pe.L Pe.γ Pe.δ h wBar) p (fun _ => B₀)) (hinc : IncoherentGateH Pe)
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
      (∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer
          (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime) B RD hG layer hLayer E hord))
          (bundleBotFamOf B RD hG layer hLayer hprime hR (botSffOf B RD hG layer hLayer hprime E hord))
          (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
        W2.TermCertW (A := A) B hG (kparOf Pe.L Pe.γ Pe.δ h wBar) (Lvl.top B) (modPsi b lam ψ)
          (openTop (WaveTurbulence.VineEstS3.Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
            (layer (RD.coreBranch hG a).toNode : ℝ))
          (WaveTurbulence.VineEstS3.Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
            Pe.L Pe.γ Pe.η) β') ∧
      ‖(coupling Pe.d Pe.L Pe.γ Pe.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ * β' ≤
        ENNReal.ofReal ((1 + |lam|) ^ (6 * Pe.η ^ 6) * ((engNs Pe.η Pe.C₁ Km Kr * Real.sqrt Pe.δ) ^ clLocalOrder2 RD hG R *
          (Kb ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card *
          Pe.L ^ (-(Pe.η ^ 8 * ((cohmolIndex B RD hG layer +
            (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
            Pe.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7)) *
          regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

/-- **`UniformTermCertTargetK`** (the hypothesis of the V5 final assembly, proved by W2 as `uniformTermCertK`): in prefix form, up to
the engine constant `c0` and the row constants `Km, Kr ≥ 1` (fixed after `c0`, before `ν, δ, D, L`), for every engine parameter
`Pe = ⟨d,γ,η,φin,τ,φ,c0,ν,δ,D,C₂,L⟩` with `0 < δ`, `τ = D δ`, `2 ≤ L` and the ambient engine data `AmbP 6561 Pe`
(`SumintMixParDoubledAt`, `η ≤ 1/5`-type bounds), `UniformTermCertAtK 6561 Pe Km Kr Kb`.  **R78 amendment**: the bad-vine factor `Kb ^ bb` (`bb` = number of bad vines,
`Kb ≥ 1` chosen after `ν, δ, D`, before `C₂, L`; it absorbs the clock-radius dependence `Rb ~ D + 1` of the kind-2 joint rows) is absorbed by `C₂ ≥ countKp D · Kb` in `Final/Core`, `Final/Prefix`. -/
def UniformTermCertTargetK : Prop :=
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
    UniformTermCertAtK 6561 (⟨d, γ, η, φin, τstar, φ, c0, ν, δ, D, C₂, L⟩ : WTParams) Km Kr Kb

end WaveTurbulence.VineEstS5C.P4.Final
