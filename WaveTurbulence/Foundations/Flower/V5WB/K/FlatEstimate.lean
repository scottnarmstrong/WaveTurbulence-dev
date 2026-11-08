/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WB.Common
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.Statements
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.PosLimit

public import WaveTurbulence.Foundations.Flower.V5WB.K.FlatBound
public import WaveTurbulence.Foundations.Flower.V5WB.W2.FinalS
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Trunc
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Mono

/-! The weighted flat observable at the original V5 C2 exponents.
This is an estimate of flatFnRMX, conditional only on the approved W2
certificate input and the standing regular-object gates. It is not yet the
estimate of twistedRecenteredModCX: that requires the weighted class identity.
-/
/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceK/FlatEstimate.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

@[expose] public section
namespace WaveTurbulence.Flower.V5WB
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

/-- `VineFlatC2MX` with `0 < B₀` (the form the certificate `UniformTermCertAtK` binds, R105 F8). -/
def VineFlatC2MXPos (P : WTParams) : Prop :=
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
    EnginePullback (Lvl.top B).region P.L wBar m mass →
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

theorem vineFlatC2MXPos_core (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKS 6561 Pe Km Kr Kb)
    (htop : Flower.Stage1W.TopIncoherentDecayAt Pe)
    (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineFlatC2MXPos ({Pe with C₁ := C₁} : WTParams) := by
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
    (fun ψ hψ tt htt E' hE' => W2.habsW (P := Pe) (A := 6561) B hG _ rfl (Lvl.top B) _ rfl (spatialMul m (modPsi b lam ψ))
        (termCertW_mul B hG _ (Lvl.top B) (modPsi b lam ψ) (hcert ψ hψ) m hpull) tt htt E' hE')
    (D := Pe.D) hp.le ?_ ?_ ?_ ?_ ?_ hC₁ ((le_div_iff₀ hKb0).2 hC₂)) (le_of_eq ?_)
  · intro ψ hψ
    exact (W2.termBoundW (P := Pe) (A := 6561) B hG _ rfl rfl rfl (Lvl.top B) (G.sign a.toNode) (G.sign a.toNode) rfl rfl
      (spatialMul m (modPsi b lam ψ))
        (termCertW_mul B hG _ (Lvl.top B) (modPsi b lam ψ) (hcert ψ hψ) m hpull)).trans (by
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
theorem vineFlatC2MX_of_pos (P : WTParams) (H : VineFlatC2MXPos P) : VineFlatC2MX P := by
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

theorem vineFlatC2MX_core (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKS 6561 Pe Km Kr Kb)
    (htop : Flower.Stage1W.TopIncoherentDecayAt Pe)
    (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineFlatC2MX ({Pe with C₁ := C₁} : WTParams) :=
  vineFlatC2MX_of_pos _ (vineFlatC2MXPos_core Pe C₁ Km Kr Kb hKm hKr hKb hR hgate hinc hUC htop hc0 hη0 hη1 hL hC₁ hC₂)

end WaveTurbulence.Flower.V5WB
