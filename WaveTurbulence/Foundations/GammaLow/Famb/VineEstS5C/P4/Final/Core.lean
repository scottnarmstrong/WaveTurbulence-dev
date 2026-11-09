/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Trunc
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Mono
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.PosLimit
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Core
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3FinalH
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Core` (sha256 e77955c832eb25ba…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # V5 FINAL (f1, kind-generic): `VineEstCanonLayerC2MK` at fixed parameters from `UniformTermCertAtK`

`vineEstCanonLayerC2MK_core`: for the statement parameters `PF = ⟨d,γ,η,φin,τ,φ,C₁,ν,δ,D,C₂,L⟩`, the engine parameters `Pe` (same with
`C₁ := c₀`), the coherent and incoherent gates at `Pe`, `UniformTermCertAtK 6561 Pe Km Kr Kb`, `C₁ ≥ (ccη+1)·countKc·Nₛ`,
`C₂ ≥ countKp D · Kb`: `VineEstCanonLayerC2MK PF` (every `kind : Bool`, premise `CanonicalObject p kind`).
(Conditional helper: `UniformTermCertAtK` is W2's output, `uniformTermCertK`.)
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Final WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Final
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
open scoped ENNReal

set_option linter.unusedSectionVars false

/-- `VineEstCanonLayerC2MK` with `0 < B₀` (R105 F8: the certificate binds `0 < B₀`; the `0 ≤ B₀` statement follows by the limit
argument `vineEstCanonLayerC2MK_of_pos`, as in `BaseLayer.layerBound_noTwist`). -/
def VineEstCanonLayerC2MKPosΓ (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 < B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ),
    RowCoherentΓ hM9 B RD hG layer hLayer (step3WΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (WaveTurbulence.VineEstS3.Eng.outBox (step3DΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (WaveTurbulence.VineEstS3.Eng.outSet (step3DΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC G a (canonFinsetK p kind (startStateΓ B RD hG layer hLayer) (chainStartΓ B))
        P.L P.γ P.δ h wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndexΓ B RD hG layer +
        (step3DΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (assemblyShapeΓ hM9 B).nor i = false).card))

theorem vineEstCanonLayerC2MKPos_coreΓ (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKΓ (γF := γF) 6561 Pe Km Kr Kb)
    (hd : 1 ≤ Pe.d) (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineEstCanonLayerC2MKPosΓ (γF := γF) ({Pe with C₁ := C₁} : WTParams) := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam hcoh
  have hL1 : 1 ≤ Pe.L := by linarith
  have hB : ProfileBound Pe (truncF p h) (fun _ => B₀) p := fun r hr => ⟨hB₀.le, by rw [truncF_eq h r hr]; exact hh r hr⟩
  have E : GateEnv Pe (kparOf Pe.L Pe.γ Pe.δ (truncF p h) wBar) p (fun _ => B₀) :=
    ⟨hgate, hB, hp, rfl, by linarith, by linarith, hc0⟩
  have hcohE : RowCoherentΓ hM9 B RD hG layer hLayer
      (step3WΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.δ (truncF p h) p := hcoh
  have hN : ∀ k, Pe.N k = ({Pe with C₁ := C₁} : WTParams).N k := fun k => (N_largeConstants Pe C₁ Pe.C₂ k).symm
  have hordE : (RD.garden hG).order ≤ Pe.N (p + 1) ^ 4 := by rw [hN]; exact hord
  have hl1E : clLocalOrder1 R ≤ Pe.N 1 ^ 4 := by rw [hN]; exact hl1
  obtain ⟨β', hcert, hβ'⟩ := hUC (truncF p h) B₀ wBar hB₀ E hinc hprime hM9 B RD hG layer hLayer kind hcan hlay hordE hl1E centre lam hR hcohE
  have hF' : ∀ k : ℕ, Summable fun m : Fin Pe.d → ℤ => |truncF p h k (wBar + latticePoint Pe.L m)| := by
    intro k
    by_cases hk : k ≤ p
    · simpa [truncF, hk] using summable_layer_coset hB hd hL1 hk wBar
    · simp [truncF, hk]
  have hAl : ∀ x, stateLayer (startStateΓ B RD hG layer hLayer) x ≤ p := by
    rw [stateLayer_startStateΓ]; exact hlay
  have hEq : (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom Pe.d) => Cont.twistedRecenteredModC G a
        (canonFinsetK p kind (startStateΓ B RD hG layer hLayer) (chainStartΓ B)) Pe.L Pe.γ Pe.δ h wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      clsFnRMΓ (p := p) (kind := kind) B RD hG layer hLayer lam (G.sign a.toNode) (kparOf Pe.L Pe.γ Pe.δ (truncF p h) wBar) hprime
        (G.sign a.toNode) := by
    rw [← twistedRecenteredModC_eq_clsFnRMΓ (p := p) (kind := kind) B RD hG layer hLayer hprime lam Pe.L Pe.γ Pe.δ (truncF p h) wBar
      (by linarith) hF']
    funext tt E
    exact twistedRecenteredModC_congr_F (startStateΓ B RD hG layer hLayer) hprime (chainStartΓ B) hAl a _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun r hr => (truncF_eq h r hr).symm)
  refine (le_of_eq (congrArg (XNorm00Restr _ _ _) hEq)).trans ?_
  have hqo : ∀ c, ((step3DΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).qOut c : ℝ)
      = ((qOutOf RD hG layer a b R c : ℕ) : ℝ) := fun c => rfl
  have hKb0 : 0 < Kb := by linarith
  refine le_trans (wpF_classBMΓ (C₂ := Pe.C₂ / Kb) (Λ := (1 + |lam|) ^ (6 * Pe.η ^ 6)) (Ns := engNs Pe.η Pe.C₁ Km Kr) (δ := Pe.δ) (C₁ := C₁)
    (Lp := Kb ^ (Finset.univ.filter fun i => (assemblyShapeΓ hM9 B).nor i = false).card *
      Pe.L ^ (-(Pe.η ^ 8 * ((cohmolIndexΓ B RD hG layer +
        (step3DΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        Pe.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7))
    (lf := regionLeafSize RD hG R layer hLayer (fun _ => B₀)) (p := p) B RD hG layer hLayer (hprime' := hprime) hM9 hR E hordE lam (G.sign a.toNode) (ne_of_gt (show (0:ℝ) < Pe.L by linarith))
    (G.sign a.toNode) (fun c => ((qOutOf RD hG layer a b R c : ℕ) : ℝ))
    (Bx := WaveTurbulence.VineEstS3.Eng.outBox
      (step3DΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
    (fun tt ht c => ⟨(ht.1 c).1, (ht.1 c).2⟩)
    (K := WaveTurbulence.VineEstS3.Eng.outSet
      (step3DΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.η)
    (WaveTurbulence.VineEstS3.Eng.countable_outSet _ _ _ _) (fun tt ht => ⟨(ht.1 0).1, (ht.1 0).2⟩)
    (fun ψ hψ tt htt E' hE' => W2.habsWΓ (A := 6561) B hG _ rfl (LvlΓ.top B) _ rfl (modPsi b lam ψ) (hcert ψ hψ) tt htt E' hE')
    (D := Pe.D) hp.le ?_ ?_ ?_ ?_ ?_ hC₁ ((le_div_iff₀ hKb0).2 hC₂)) (le_of_eq ?_)
  · intro ψ hψ
    exact (W2.termBoundWΓ (A := 6561) B hG _ rfl rfl rfl (LvlΓ.top B) (G.sign a.toNode) (G.sign a.toNode) rfl rfl
      (modPsi b lam ψ) (hcert ψ hψ)).trans hβ'
  · exact Real.rpow_nonneg (by positivity) _
  · have h1 : 0 < Km := by linarith
    have h2 : 0 < Kr := by linarith
    have h3 : 0 < Pe.C₁ := by linarith
    unfold engNs
    positivity
  · exact mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  · exact regionLeafSize_const_nonneg RD hG R layer hLayer hB₀.le
  · congr 1
    rw [div_pow]
    field_simp

/-- **F8 limit argument**: the `0 ≤ B₀` statement from the `0 < B₀` one (`B₀ + ε`, `ε → 0`). -/
theorem vineEstCanonLayerC2MK_of_posΓ (P : WTParams) (H : VineEstCanonLayerC2MKPosΓ (γF := γF) (rowSel := VineEst.RowSel.plain) P) : VineEstCanonLayerC2MKΓ (γF := γF) P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam hcoh
  have e : ∀ a b c d e0 : ℝ, a * (b * c * d * e0) = (a * (b * c * e0)) * d := fun a b c d e0 => by ring
  conv_rhs => rw [e]
  refine le_regionLeafSize_of_forall_pos RD hG layer hLayer (fun _ => B₀) _ (fun ε hε => ?_)
  refine le_of_le_of_eq ?_ (congrArg ENNReal.ofReal (e _ _ _ _ _))
  exact H hp h (B₀ + ε) (by linarith) (fun r hr => (hh r hr).trans (ENNReal.ofReal_le_ofReal (by linarith)))
    hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam hcoh

theorem vineEstCanonLayerC2MK_coreΓ (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKΓ (γF := γF) (rowSel := VineEst.RowSel.plain) 6561 Pe Km Kr Kb)
    (hd : 1 ≤ Pe.d) (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineEstCanonLayerC2MKΓ (γF := γF) ({Pe with C₁ := C₁} : WTParams) :=
  vineEstCanonLayerC2MK_of_posΓ _ (vineEstCanonLayerC2MKPos_coreΓ Pe C₁ Km Kr Kb hKm hKr hKb hR hgate hinc hUC hd hc0 hη0 hη1 hL hC₁ hC₂)

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Final
