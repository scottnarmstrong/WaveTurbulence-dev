/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.V5W.B2
public import WaveTurbulence.Foundations.Flower.V5WB.K.FlatEstimate
public import WaveTurbulence.Foundations.Flower.V5WB.K.FlatHalf
public import WaveTurbulence.Foundations.Flower.V5WB.K.FlatPrefix
public import WaveTurbulence.Foundations.Flower.V5WB.Final
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Core
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.WinChain

/-! # FLOWER-LOW (packet L8), item I3 (B3): the weighted vine estimate (V5W) over `𝒱_γ`

Main's `Flower.V5W*` declarations that depend on the chain assembly or the chart obligation (the cone of
`V5WT.v5FrontierClassBound` through `VineEstS2.CLChainAssembly`, `VINEPARAM`, `ChainPiece`), copied by source
(sha256 in `COPIED-SHA256SUMS`) onto L5b's `𝒱_γ` port of the vine estimate (`GammaLow.Famb`, names suffixed `Γ`),
with L5b's rules: `CLChainAssembly` ↦ `Famb.VineEstS2.CLChainAssemblyΓ γF`, `ChainPiece` ↦ `ChainPieceΓ γF`,
`VINEPARAM` ↦ `Famb.NormalChartSupply γF`, `.vineType` ↦ `.label`; copied names get the suffix `Γ`. Everything else
(weights, frontier filters, flat estimates, kernels) is main's, by import. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

/-- `VineFlatC2MXΓ` with `0 < B₀` (the form the certificate `Famb.VineEstS5C.P4.Final.UniformTermCertAtKΓ` binds, R105 F8). -/
def VineFlatC2MXPosΓ (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D →
    (rowSel.weighted = true → rowSel.p = p ∧ Flower.Stage1W.GPresented (32 * P.d) (rowSel.g P.d) rowSel.cψ) →
    ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 < B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (mass : ℝ), 0 ≤ mass →
    EnginePullbackΓ (γF := γF) (Famb.VineEstS5C.LvlΓ.top B).region P.L wBar m mass →
    Famb.VineEstS3.RowCoherentΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (flatFnRMXΓ (p := p) (kind := kind) B RD hG layer hLayer m lam (G.sign a.toNode)
        (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode)) ≤
    ENNReal.ofReal mass * ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((Famb.VineEstS3.cohmolIndexΓ B RD hG layer +
        (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

theorem vineFlatC2MXPos_coreΓ (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKSΓ (γF := γF) 6561 Pe Km Kr Kb)
    (htop : Flower.Stage1W.TopIncoherentDecayAt Pe)
    (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineFlatC2MXPosΓ (γF := γF) ({Pe with C₁ := C₁} : WTParams) := by
  intro p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh
  have hL1 : 1 ≤ Pe.L := by linarith
  have hB : ProfileBound Pe (truncF p h) (fun _ => B₀) p := fun r hr => ⟨hB₀.le, by rw [truncF_eq h r hr]; exact hh r hr⟩
  have E : GateEnv Pe (kparOf Pe.L Pe.γ Pe.δ (truncF p h) wBar) p (fun _ => B₀) :=
    ⟨hgate, hB, hp, rfl, by linarith, by linarith, hc0⟩
  have hcohE : Famb.VineEstS3.RowCoherentΓ hM9 B RD hG layer hLayer
      (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.δ (truncF p h) p := hcoh
  have hN : ∀ k, Pe.N k = ({Pe with C₁ := C₁} : WTParams).N k := fun k => (LGSpine.N_largeConstants Pe C₁ Pe.C₂ k).symm
  have hordE : (RD.garden hG).order ≤ Pe.N (p + 1) ^ 4 := by rw [hN]; exact hord
  have hl1E : clLocalOrder1 R ≤ Pe.N 1 ^ 4 := by rw [hN]; exact hl1
  obtain ⟨β', hcert, hβ'⟩ := hUC (truncF p h) B₀ wBar hB₀ E hinc (fun hw => ⟨(hsp hw).1, (hsp hw).2, htop⟩) hprime hM9 B RD hG layer hLayer kind hcan hlay hordE hl1E centre lam hR hcohE
  have hKb0 : 0 < Kb := by linarith only [hKb]
  refine le_trans (wpF_flatBMXΓ (C₂ := Pe.C₂ / Kb) (Λ := mass * (1 + |lam|) ^ (6 * Pe.η ^ 6)) (Ns := engNs Pe.η Pe.C₁ Km Kr) (δ := Pe.δ) (C₁ := C₁)
    (Lp := Kb ^ (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card *
      Pe.L ^ (-(Pe.η ^ 8 * ((Famb.VineEstS3.cohmolIndexΓ B RD hG layer +
        (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        Pe.η ^ 2 * ((Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7))
    (lf := regionLeafSize RD hG R layer hLayer (fun _ => B₀)) (p := p) (kind := kind) B RD hG layer hLayer (hprime' := hprime) hM9 hR E hordE m lam (G.sign a.toNode)
    (G.sign a.toNode) (fun c => ((qOutOf RD hG layer a b R c : ℕ) : ℝ))
    (Bx := WaveTurbulence.VineEstS3.Eng.outBox
      (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
    (fun tt ht c => ⟨(ht.1 c).1, (ht.1 c).2⟩)
    (K := WaveTurbulence.VineEstS3.Eng.outSet
      (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.η)
    (WaveTurbulence.VineEstS3.Eng.countable_outSet _ _ _ _) (fun tt ht => ⟨(ht.1 0).1, (ht.1 0).2⟩)
    (fun ψ hψ tt htt E' hE' => Famb.VineEstS5C.P4.W2.habsWΓ (P := Pe) (A := 6561) B hG _ rfl (Famb.VineEstS5C.LvlΓ.top B) _ rfl (spatialMul m (modPsi b lam ψ))
        (termCertW_mulΓ B hG _ (Famb.VineEstS5C.LvlΓ.top B) (modPsi b lam ψ) (hcert ψ hψ) m hpull) tt htt E' hE')
    (D := Pe.D) hp.le ?_ ?_ ?_ ?_ ?_ hC₁ ((le_div_iff₀ hKb0).2 hC₂)) (le_of_eq ?_)
  · intro ψ hψ
    exact (Famb.VineEstS5C.P4.W2.termBoundWΓ (P := Pe) (A := 6561) B hG _ rfl rfl rfl (Famb.VineEstS5C.LvlΓ.top B) (G.sign a.toNode) (G.sign a.toNode) rfl rfl
      (spatialMul m (modPsi b lam ψ))
        (termCertW_mulΓ B hG _ (Famb.VineEstS5C.LvlΓ.top B) (modPsi b lam ψ) (hcert ψ hψ) m hpull)).trans (by
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

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

/-- **F8 limit argument for the flat form** (copy of `Famb.VineEstS5C.P4.Final.vineEstCanonLayerC2MK_of_posΓ`): `0 ≤ B₀` from `0 < B₀`. -/
theorem vineFlatC2MX_of_posΓ (P : WTParams) (H : VineFlatC2MXPosΓ (γF := γF) P) : VineFlatC2MXΓ (γF := γF) P := by
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

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

theorem vineFlatC2MX_coreΓ (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKSΓ (γF := γF) 6561 Pe Km Kr Kb)
    (htop : Flower.Stage1W.TopIncoherentDecayAt Pe)
    (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineFlatC2MXΓ (γF := γF) ({Pe with C₁ := C₁} : WTParams) :=
  vineFlatC2MX_of_posΓ _ (vineFlatC2MXPos_coreΓ Pe C₁ Km Kr Kb hKm hKr hKb hR hgate hinc hUC htop hc0 hη0 hη1 hL hC₁ hC₂)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

/-- **R54 (ii) from (i), modulated, for every selector** (the selector is bound after the record). -/
theorem vineFlatHalfMX_of_C2MXΓ (H : WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatC2MXΓ (γF := γF) P) :
    WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXΓ (γF := γF) P := by
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
  have key : VineFlatC2MXΓ (γF := γF) ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ := H4 L hLL₀
  intro p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh
  refine (key hp hsp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have hδ0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  exact half_of_C2_real (pow_nonneg (mul_nonneg (by linarith) hδ0) _)
    (regionLeafSize_const_nonneg RD hG R layer hLayer hB₀) hLpos (C2_pow_le _ hη.1 hC₂ hLC)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

/-- **The weighted flat estimate for every selector, on the prefix** (V5W-A's `vineFlatC2MX_of_uniformCertΓ` with the
selector certificate `UniformTermCertTargetKSΓ` and INC-TOP's gate). -/
theorem vineFlatC2MX_of_uniformCertΓ (hU : UniformTermCertTargetKSΓ (γF := γF)) (hG : LeafwiseCoherentApproximationGate)
    (hI : LeafwiseIncoherentDecayGate) (hR : RealityAll) (hT : Flower.Stage1W.TopIncoherentDecayGateR) :
    WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatC2MXΓ (γF := γF) P := by
  have hI : WTPrefix fun P => LeafwiseIncoherentDecayAt P ∧ Flower.Stage1W.TopIncoherentDecayAtR P :=
    prefix_and hI hT leafwiseIncoherentDecay_largeConstantMonotone
      Flower.Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone
  intro d hd γ hγ
  obtain ⟨ηU, hηU, hUa⟩ := hU d hd γ hγ
  obtain ⟨ηS, hηS, hSa⟩ := sumintMixParDoubled d hd γ hγ
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
    sumintMixPar_mono 6561 PS c₀ C₂ hCS hC₂S hδ.1 hL2 hCSc hC₂S' (hSd L hLS')
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
  have hUC : UniformTermCertAtKSΓ (γF := γF) 6561 Pe Km Kr Kb := hUb' C₂ L hL2 hAmb
  have key : VineFlatC2MXΓ (γF := γF) ({Pe with C₁ := C₁} : WTParams) := vineFlatC2MX_coreΓ Pe C₁ Km Kr Kb hKm hKr hKb hR hgate hinc
    hUC htop hc₀ hη0 (by show η ≤ 1 / 2; linarith) hL2 (le_max_right _ _) hC₂K
  exact @key

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

/-- **`WTPrefix VineFlatHalfMXΓ`** for every selector, from the same inputs. -/
theorem vineFlatHalfMX_of_uniformCertΓ (hU : UniformTermCertTargetKSΓ (γF := γF)) (hG : LeafwiseCoherentApproximationGate)
    (hI : LeafwiseIncoherentDecayGate) (hR : RealityAll) (hT : Flower.Stage1W.TopIncoherentDecayGateR) :
    WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXΓ (γF := γF) P :=
  vineFlatHalfMX_of_C2MXΓ (vineFlatC2MX_of_uniformCertΓ hU hG hI hR hT)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback enginePullback_one)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_topDarts_le)
open WaveTurbulence.Flower.V5W (nodeRowIncoh twistedRecenteredFW topFilterMass V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal FourierTransform
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}
variable {w d : ℕ} {ι : Type*} {U : Finset (GBranch _)} 

/-- **The engine pullback of the masked, normalized bond weight of a block.** -/
theorem enginePullback_bWNΓ (X : FamilyReconstruction w ι) {U : Finset (GBranch X.skeleton.tree)}
    {a b : GBranch X.skeleton.tree} (R : CLRegionData X.skeleton U a b) (hU : X.skeleton.molecule.IsBlock U a b)
    (L : ℝ) (base : Mom d) (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (hcψ : 1 ≤ cψ)
    (hpres : ∃ (α : Type) (_ : MeasurableSpace α) (M : Cut2A.SpatialMeasure (Mom d) α),
      M.mass ≤ cψ ∧ ∀ x, M.value x = g x) :
    EnginePullbackΓ (γF := γF) R L base (bondWD X.skeleton (ΨX (wdOf p g cψ) X) L base (layX X) U)
      (cψ ^ (3 * U.card) * ∏ y ∈ regionDarts X.skeleton U,
        nodeNorm X.data X.plain (stateLayer X) (stateLayer_isLayering X) cψ (Mole.dartNode X.skeleton y)) := by
  classical
  have hc0 : 0 ≤ cψ := by linarith
  let T : GardenDart X.skeleton → Prop := fun y =>
    layX X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)) < p ∧ layX X (X.skeleton.molecule.atom y) = p
  have hfac : ∀ y ∈ regionDarts X.skeleton U, EnginePullbackΓ (γF := γF) R L base
      (fun z => ΨX (wdOf p g cψ) X y (layX X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)))
        (layX X (X.skeleton.molecule.atom y)) (cosetDecoration X.skeleton L base z (Mole.dartNode X.skeleton y)))
      ((if T y then cψ else 1) *
        nodeNorm X.data X.plain (stateLayer X) (stateLayer_isLayering X) cψ (Mole.dartNode X.skeleton y)) := by
    intro y _
    unfold ΨX nodeNorm
    by_cases hi : nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y) = 0
    · simp only [hi, ↓reduceIte, mul_one, wdOf]
      by_cases hy : T y
      · rw [if_pos hy]
        obtain ⟨α, _, M, hM, hv⟩ := hpres
        refine enginePullback_monoΓ R L base (enginePullback_congrΓ R L base
          (enginePullback_nodeValueΓ R L base M (Mole.dartNode X.skeleton y)) ?_) hM
        funext z
        rw [hv]
        exact (if_pos hy).symm
      · rw [if_neg hy]
        refine enginePullback_congrΓ R L base (enginePullback_oneΓ R L base) ?_
        funext z
        simp only [topPsi]
        rw [if_neg hy]
    · simp only [hi, ↓reduceIte]
      obtain ⟨α, _, M, hM, hv⟩ := const_presented (d := d)
        (cψ ^ ((nodeRowExp X.data X.plain (stateLayer X) (stateLayer_isLayering X)
          (Mole.dartNode X.skeleton y) : ℝ) / 2))
      have hr : 0 ≤ cψ ^ ((nodeRowExp X.data X.plain (stateLayer X) (stateLayer_isLayering X)
          (Mole.dartNode X.skeleton y) : ℝ) / 2) := Real.rpow_nonneg hc0 _
      have h1 : (1 : ℝ) ≤ if T y then cψ else 1 := by split_ifs <;> linarith
      refine enginePullback_monoΓ R L base (enginePullback_congrΓ R L base
        (enginePullback_nodeValueΓ R L base M (Mole.dartNode X.skeleton y)) ?_) ?_
      · funext z
        rw [hv]
        rfl
      · rw [abs_of_nonneg hr] at hM
        exact hM.trans (le_mul_of_one_le_left hr h1)
  have hprod := enginePullback_finsetProdΓ R L base (regionDarts X.skeleton U) _ _ hfac
  rw [Finset.prod_mul_distrib] at hprod
  have hmass : (∏ y ∈ regionDarts X.skeleton U, if T y then cψ else 1) =
      cψ ^ (topDarts X.skeleton (layX X) U p).card := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rfl
  rw [hmass] at hprod
  refine enginePullback_monoΓ R L base hprod ?_
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hcψ ?_)
    (Finset.prod_nonneg fun y _ => ?_)
  · have := card_topDarts_le hU (layX X) p
    omega
  · unfold nodeNorm
    split_ifs
    · exact zero_le_one
    · exact Real.rpow_nonneg hc0 _

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback enginePullback_one)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_topDarts_le)
open WaveTurbulence.Flower.V5W (nodeRowIncoh twistedRecenteredFW topFilterMass V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal FourierTransform
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}

/-- **The `S = none` half of the weighted vine class bound at a record**, from the weighted flat estimate at that record
for every row selector. -/
theorem v5FrontierClassBoundNoneAt_of_flatΓ (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (H : ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXΓ (γF := γF) P) : V5FrontierClassBoundOnAtΓ (γF := γF) (· = none) P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam
    g cψ hcψ hpres hreal S hS hSpos hcoh
  subst hS
  have hc0 : 0 ≤ cψ := le_trans zero_le_one hcψ
  obtain ⟨αg, _, Mg, hMg, hvg⟩ := Flower.V5WA.presented_of_gPresented hc0 (hpres a.1.1)
  have hgle : ∀ x, ‖g a.1.1 x‖ ≤ cψ := fun x => by
    rw [← hvg]
    exact (Mg.norm_value_le x).trans hMg
  let I : VineEst.RowSel () := selW p (g a.1.1) cψ hcψ hgle (hreal a.1.1)
  have hB : ProfileBound P (truncF p h) (fun _ => B₀) p :=
    fun r hr => ⟨hB₀, by rw [truncF_eq h r hr]; exact hh r hr⟩
  have hF : ∀ k : ℕ, Summable fun z : Fin P.d → ℤ => |truncF p h k (wBar + latticePoint P.L z)| := by
    intro k
    by_cases hk : k ≤ p
    · simpa only [truncF, ite_eq_left hk] using P2.summable_layer_coset hB hd hL hk wBar
    · simp only [truncF, ite_eq_right hk, Pi.zero_apply, abs_zero, summable_zero]
  have hAl : ∀ x, stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) x ≤ p := by
    rw [Famb.VineEstS5C.P4.stateLayer_startStateΓ]
    exact hlay
  have hbr : (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom P.d) => twistedRecenteredFW p (g a.1.1) none G a
      (canonFinsetK p kind (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) (Famb.VineEstS4.chainStartΓ B)) P.L P.γ P.δ h wBar (VineC.modW lam)
      (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
      (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      flatFnRMXΓ (rowSel := I) (p := p) (kind := kind) B RD hG layer hLayer
        (lvWΓ B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (kparOf P.L P.γ P.δ (truncF p h) wBar)
          (Famb.VineEstS5C.LvlΓ.top B)) lam (G.sign a.toNode) (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode) := by
    funext tt E
    rw [twistedRecenteredFW_none_eq p (g a.1.1) cψ hcψ hgle (hreal a.1.1)]
    refine (twistedRecenteredModCX_congr_F (rowSel := I) (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) hprime (Famb.VineEstS4.chainStartΓ B) hAl
      a P.L P.γ P.δ h (truncF p h) wBar lam _ (tt 0) (tt 1) (tt 2) _ _ _ _ (fun r hr => (truncF_eq h r hr).symm)).trans ?_
    exact congrFun (congrFun (twistedRecenteredModCX_bond_eq_flatFnΓ (rowSel := I) (p := p) (kind := kind) B RD hG
      layer hLayer hprime lam (wdOf p (g a.1.1) cψ) cψ hc0
      (fun q q' k => by
        show ‖topPsi p (g a.1.1) q q' k‖ ≤ cψ
        unfold topPsi
        split_ifs
        · exact hgle k
        · simpa using hcψ)
      P.L P.γ P.δ (truncF p h) wBar (by linarith only [hL]) hF) tt) E
  set mass : ℝ := cψ ^ (3 * U.card) * ∏ y ∈ regionDarts G U,
    nodeNorm (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain
      (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) cψ
      (Mole.dartNode G y) with hmassd
  have hpull : EnginePullbackΓ (γF := γF) (Famb.VineEstS5C.LvlΓ.top B).region P.L wBar
      (lvWΓ B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (kparOf P.L P.γ P.δ (truncF p h) wBar)
        (Famb.VineEstS5C.LvlΓ.top B)) mass :=
    enginePullback_bWNΓ (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) (Famb.VineEstS5C.LvlΓ.top B).region B.isBlock P.L wBar p (g a.1.1) cψ hcψ
      ⟨αg, inferInstance, Mg, hMg, hvg⟩
  have hrow : ∏ y ∈ regionDarts G U,
      nodeNorm (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain
        (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) cψ
        (Mole.dartNode G y) =
      rowNorm cψ (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain R
        (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) :=
    prod_nodeNorm_regionDarts _ _ _ _ cψ hc0 B.isBlock R
  have hrowle := rowNorm_le hcψ (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain
    B.isBlock R (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer))
  have hrow0 : 0 ≤ rowNorm cψ (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain R
      (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) :=
    hrow ▸ Finset.prod_nonneg fun y _ => by unfold nodeNorm; split_ifs <;> positivity
  have hmass0 : 0 ≤ mass := by rw [hmassd, hrow]; positivity
  have hsp : I.weighted = true → I.p = p ∧ GPresented (32 * P.d) (I.g P.d) I.cψ := fun _ =>
    ⟨rfl, by show GPresented (32 * P.d) (gAt (g a.1.1) P.d) cψ; rw [gAt_self]; exact hpres a.1.1⟩
  have key := @H () I p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1
    centre wBar lam _ mass hmass0 hpull hcoh
  rw [hbr]
  refine key.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hU1 : clLocalOrder1 R ≤ U.card := Finset.card_erase_le
  have hT := one_le_topFilterMass
  calc mass = cψ ^ (3 * U.card) * rowNorm cψ (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data
        (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain R (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer))
        (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) := by rw [hmassd, hrow]
    _ ≤ cψ ^ (3 * U.card) * cψ ^ (2 * clLocalOrder2 RD hG R + 2 * clLocalOrder1 R) :=
        mul_le_mul_of_nonneg_left hrowle (by positivity)
    _ = cψ ^ (3 * U.card + (2 * clLocalOrder2 RD hG R + 2 * clLocalOrder1 R)) := (pow_add _ _ _).symm
    _ ≤ cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) := pow_le_pow_right₀ hcψ (by omega)
    _ ≤ cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * topFilterMass :=
        le_mul_of_one_le_right (by positivity) hT

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback enginePullback_one)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_topDarts_le)
open WaveTurbulence.Flower.V5W (nodeRowIncoh twistedRecenteredFW topFilterMass V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal FourierTransform
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}

/-- **V5W-B: the `S = none` half of the weighted vine class bound** (supplement Lemma 5.3, V5 form), in the gate form of
the frozen `WTPrefix`, from main's selector certificate (`uniformTermCertKSΓ`), main's leafwise regular-object gates,
`RealityAll` and INC-TOP's normalized incoherent gate. -/
theorem v5FrontierClassBoundNoneΓ : WTPrefix (V5FrontierClassBoundOnAtΓ (γF := γF) (· = none)) := by
  have H := vineFlatHalfMX_of_uniformCertΓ (γF := γF) (uniformTermCertKSΓ (γF := γF)) Spine.leafwise_coherent_approximation
    Spine.leafwise_incoherent_decay VineEstS5C.P1.realityAll IncTop.topIncoherentDecayGateR
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  exact v5FrontierClassBoundNoneAt_of_flatΓ ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩
    (by change 1 ≤ d; omega) (by change 1 ≤ L; linarith only [hL₀, hL]) (H4 L hL)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback enginePullback_one)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_topDarts_le)
open WaveTurbulence.Flower.V5W (nodeRowIncoh twistedRecenteredFW topFilterMass V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal FourierTransform
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}

/-- **The gate `V5FrontierClassBoundΓ`** from the `S ≠ none` half (the region-top stem filter, V5W-T). -/
theorem v5FrontierClassBound_of_topΓ (hT : WTPrefix (V5FrontierClassBoundOnAtΓ (γF := γF) (· ≠ none))) : V5FrontierClassBoundΓ (γF := γF) :=
  v5FrontierClassBound_of_halvesΓ v5FrontierClassBoundNoneΓ hT

end

end WaveTurbulence.GammaLow.Flower
