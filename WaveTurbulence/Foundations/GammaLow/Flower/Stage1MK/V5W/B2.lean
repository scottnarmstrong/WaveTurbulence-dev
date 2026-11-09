/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.V5W.B1
public import WaveTurbulence.Foundations.Flower.V5WB.W2.RowsS
public import WaveTurbulence.Foundations.Flower.V5WB.W2.NatS
public import WaveTurbulence.Foundations.Flower.V5WB.W2.RecS
public import WaveTurbulence.Foundations.Flower.V5WB.W2.FinalS
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.HFree.Inst
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyAtoms
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLClockReindex
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Momenta
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClauseA
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Facts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Final
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowOrder
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowSum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.NativeRowsH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P2.Dict2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Bot.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Bot.Terms
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.BundleExp
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.BotCount
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W13.SFFam
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.AmbEng
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecBlock
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecCert
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecCertDefs
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecContract
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecEng
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecFinal
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecFinal2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecFree
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecHX3
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecProd
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecRegion
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecRow
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecRowsBnd
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecSpec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecSz7
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RowMatch
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.TermNat1
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.TermNat2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3FinalH

/-! # FLOWER-LOW (packet L8), item I3 (B2): the weighted vine estimate (V5W) over `𝒱_γ`

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
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W2 MeasureTheory
open scoped ENNReal
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable {hM9 : Famb.NormalChartSupply γF} {B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n} {RD : ReconstructionData G} {hG : G.IsPlain}
  {layer : GNode (RD.forest hG) → ℕ} {hLayer : IsLayering (RD.garden hG) layer}
variable {P : WTParams} {p : ℕ}

/-- **Row bound, selected couples** (layer family, leaf cost). -/
theorem coupleRow_leaf_leSΓ (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B) P.d) {h : ℕ → Mom P.d → ℝ}
    {Bh : ℕ → ℝ} (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (hsel : SelOK P p)
    (hq : W.q = Famb.VineEstS2.assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (v : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx)
    (hel : Famb.VineEstS3.CoupleEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d)
      (timeBox (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).1
        (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).2) Set.univ
      (fun ts k => VineEst.selCoupleRow P.L P.γ P.δ h RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1
        (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).size / 2) (Famb.VineEstS3.rowCoupleGΓ hM9 B RD hG layer hLayer v) *
        layerCost Bh (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v)) := by
  by_cases hc : rowSel.weighted = true ∧ Famb.VineEstS3.rowCoupleGΓ hM9 B RD hG layer hLayer v ≠ 0
  · obtain ⟨hwt, hg0⟩ := hc
    obtain ⟨hpp, hpres, htop⟩ := hsel hwt
    have hel' := hel
    obtain ⟨hqp, hq'p, hn, hr0, hr1, -⟩ := hel'
    have hwf : (Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).wf = true := RD.couple_wf _
    have hsize : (Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).size = 2 * ((Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).size / 2) :=
      (Nat.two_mul_div_two_of_even (code_size_even _)).symm
    have hdec : (Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).Decodes (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden :=
      Famb.VineEstS3.rowCouple_decodesΓ v
    have hord : (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden.order =
        2 * ((Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).size / 2) :=
      (IncohInst.couple_size_eq_order _ hdec).trans hsize
    have hlay' : ∀ x, (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _
    obtain ⟨e0, e1⟩ := coupleRootParents_rowQΓ hM9 B RD hG layer hLayer W hq hqo P.L P.γ P.δ h p v
    have hg0' : Flower.V5W.coupleIncoh RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1 ≠ 0 := hg0
    have hexp : 2 * (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden.order + 2 =
        4 * ((Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).size / 2) + 2 := by rw [hord]; ring
    have hfun : (fun ts k => VineEst.selCoupleRow P.L P.γ P.δ h RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1
        (ts 0) (ts 1) k) = fun (ts : Fin 2 → ℝ) k =>
          (((rowSel.cψ ^ (4 * ((Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).size / 2) + 2))⁻¹ : ℝ) : ℂ) *
          Stage1W.coupleLeavesTop P.L P.γ P.δ p (rowSel.g P.d)
            (Flower.V5W.coupleRootParents p RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1 0)
            (Flower.V5W.coupleRootParents p RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1 1)
            (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v)
            (LGSpine.layerProfiles (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v) h) (ts 0) (ts 1) k := by
      funext ts k
      unfold VineEst.selCoupleRow
      rw [KQsel_weighted hwt hg0', hpp]
      change (((rowSel.cψ ^ (2 * (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden.order + 2))⁻¹ : ℝ) : ℂ) * _ = _
      rw [hexp]
      rfl
    have hbox : timeBox (Flower.V5W.coupleRootParents p RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1 0)
        (Flower.V5W.coupleRootParents p RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1 1) =
        timeBox (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).1
          (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).2 := by rw [e0, e1]
    rw [hfun]
    have hc1 := rowSel.one_le_cψ
    have hcne : (((rowSel.cψ ^ (4 * ((Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).size / 2) + 2))⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < rowSel.cψ ^ (4 * ((Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).size / 2) + 2) := pow_pos (by linarith) _
      exact_mod_cast (inv_pos.2 this).ne'
    refine (XNormRestr_mono_theta hη6 _ _ _ _ _).trans ?_
    refine (XNormRestr_const_mul_le hcne _ _ _ _ _ _).trans ?_
    have hg1 : 1 ≤ Famb.VineEstS3.rowCoupleGΓ hM9 B RD hG layer hLayer v := Nat.one_le_iff_ne_zero.mpr hg0
    have hT := (htop p hp _ hn (rowSel.g P.d) rowSel.cψ hc1 hpres).1 (Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v) hwf hsize
      (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v) hdec hlay'
      (Flower.V5W.coupleRootParents p RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1 0)
      (Flower.V5W.coupleRootParents p RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1 1) (by rw [e0]; exact hqp) (by rw [e1]; exact hq'p)
      (by rw [e0]; exact hr0) (by rw [e1]; exact hr1) hg1 _ _
      (Flower.V5W.controlled_layerProfiles_spine hB _ hlay')
    rw [leafSizeProduct_eq_layerCost hB _ hlay', hbox] at hT
    refine (mul_le_mul' le_rfl hT).trans ?_
    rw [mul_assoc, norm_cancel hc1]
    have hL0 : 0 ≤ P.L := by linarith
    rw [ENNReal.ofReal_mul (rowB_nonneg' (P := P) hC hδ (by linarith) _ _)]
    exact mul_le_mul' (regBound_le_rowB hC hδ hL0 _ _) le_rfl
  · have hfun : (fun ts k => VineEst.selCoupleRow P.L P.γ P.δ h RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1
        (ts 0) (ts 1) k) = fun (ts : Fin 2 → ℝ) k =>
          KQstar P.L P.γ P.δ h (Famb.VineEstS3.rowCoupleLGΓ hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k := by
      funext ts k
      unfold VineEst.selCoupleRow
      rcases not_and_or.mp hc with hw' | hg0
      · exact VineEst.KQsel_of_weighted_eq_false (by simpa using hw') _ _ _ _ _ _ _ _ _ _ _
      · exact VineEst.KQsel_of_incoh_eq_zero (not_not.mp hg0) _ _ _ _ _ _ _ _ _ _
    rw [hfun]
    exact Famb.VineEstS5C.coupleRow_leaf_leΓ W hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hlay v hel

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W2 MeasureTheory
open scoped ENNReal
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable {hM9 : Famb.NormalChartSupply γF} {B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n} {RD : ReconstructionData G} {hG : G.IsPlain}
  {layer : GNode (RD.forest hG) → ℕ} {hLayer : IsLayering (RD.garden hG) layer}
variable {P : WTParams} {p : ℕ}

/-- **Row bound, selected trees** (layer family, leaf cost). -/
theorem treeRow_leaf_leSΓ (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B) P.d) {h : ℕ → Mom P.d → ℝ}
    {Bh : ℕ → ℝ} (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (hsel : SelOK P p)
    (hq : W.q = Famb.VineEstS2.assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (v : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx)
    (hel : Famb.VineEstS3.TreeEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) 0
      (timeBoxGt (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1
        (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2) Set.univ
      (fun ts k => VineEst.selTreeRow P.L P.γ P.δ h RD hG layer hLayer (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).1
        (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((Famb.VineEstS3.rowTreeΓ hM9 B RD v).size / 2) (Famb.VineEstS3.rowTreeGΓ hM9 B RD hG layer hLayer v) *
        layerCost Bh (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v)) := by
  by_cases hc : rowSel.weighted = true ∧ Famb.VineEstS3.rowTreeGΓ hM9 B RD hG layer hLayer v ≠ 0
  · obtain ⟨hwt, hg0⟩ := hc
    obtain ⟨hpp, hpres, htop⟩ := hsel hwt
    have hel' := hel
    obtain ⟨hqq, hqp, hn, hr0, hlone, -⟩ := hel'
    have hwf : (Famb.VineEstS3.rowTreeΓ hM9 B RD v).wf = true := RD.tree_wf _
    have hsize : (Famb.VineEstS3.rowTreeΓ hM9 B RD v).size = 2 * ((Famb.VineEstS3.rowTreeΓ hM9 B RD v).size / 2) :=
      (Nat.two_mul_div_two_of_even (chain_size_even _)).symm
    have hdec : (Famb.VineEstS3.rowTreeΓ hM9 B RD v).DecodesTree (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v).garden := Famb.VineEstS3.rowTree_decodesΓ v
    have hord : (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v).garden.order = 2 * ((Famb.VineEstS3.rowTreeΓ hM9 B RD v).size / 2) :=
      (decodesTree_order' hdec).trans hsize
    have hlay' : ∀ x, (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _
    have e0 := treeRootParent_rowQΓ hM9 B RD hG layer hLayer W hq hqo P.L P.γ P.δ h p v
    have hg0' : Flower.V5W.treeIncoh RD hG layer hLayer (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).1 ≠ 0 := hg0
    have hexp : 2 * (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v).garden.order + 1 =
        4 * ((Famb.VineEstS3.rowTreeΓ hM9 B RD v).size / 2) + 1 := by rw [hord]; ring
    have hfun : (fun ts k => VineEst.selTreeRow P.L P.γ P.δ h RD hG layer hLayer (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).1
        (ts 0) (ts 1) k) = fun (ts : Fin 2 → ℝ) k =>
          (((rowSel.cψ ^ (4 * ((Famb.VineEstS3.rowTreeΓ hM9 B RD v).size / 2) + 1))⁻¹ : ℝ) : ℂ) *
          Stage1W.treeLeavesTop P.L P.γ P.δ p (rowSel.g P.d)
            (Flower.V5W.treeRootParent p RD hG layer hLayer (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).1)
            (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v)
            (LGSpine.layerProfiles (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v) h) (ts 0) (ts 1) k := by
      funext ts k
      unfold VineEst.selTreeRow
      rw [KTsel_weighted hwt hg0', hpp]
      change (((rowSel.cψ ^ (2 * (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v).garden.order + 1))⁻¹ : ℝ) : ℂ) * _ = _
      rw [hexp]
      rfl
    have hbox : timeBoxGt (Flower.V5W.treeRootParent p RD hG layer hLayer (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).1)
        (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 =
        timeBoxGt (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1
          (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 := by rw [e0]
    rw [hfun]
    have hc1 := rowSel.one_le_cψ
    have hcne : (((rowSel.cψ ^ (4 * ((Famb.VineEstS3.rowTreeΓ hM9 B RD v).size / 2) + 1))⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < rowSel.cψ ^ (4 * ((Famb.VineEstS3.rowTreeΓ hM9 B RD v).size / 2) + 1) := pow_pos (by linarith) _
      exact_mod_cast (inv_pos.2 this).ne'
    refine (XNormRestr_mono_theta hη6 _ _ _ _ _).trans ?_
    refine (XNormRestr_const_mul_le hcne _ _ _ _ _ _).trans ?_
    have hg1 : 1 ≤ Famb.VineEstS3.rowTreeGΓ hM9 B RD hG layer hLayer v := Nat.one_le_iff_ne_zero.mpr hg0
    have hT := (htop p hp _ hn (rowSel.g P.d) rowSel.cψ hc1 hpres).2 (Famb.VineEstS3.rowTreeΓ hM9 B RD v) hwf hsize
      (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v) hdec hlay'
      (Flower.V5W.treeRootParent p RD hG layer hLayer (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).1)
      (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 (by rw [e0]; exact hqq) (by rw [e0]; exact hqp)
      (by rw [e0]; exact hr0) hlone hg1 _ _
      (Flower.V5W.controlled_layerProfiles_spine hB _ hlay')
    rw [leafSizeProduct_eq_layerCost hB _ hlay', hbox] at hT
    refine (mul_le_mul' le_rfl hT).trans ?_
    rw [mul_assoc, norm_cancel hc1]
    have hL0 : 0 ≤ P.L := by linarith
    rw [ENNReal.ofReal_mul (rowB_nonneg' (P := P) hC hδ (by linarith) _ _)]
    exact mul_le_mul' (regBound_le_rowB hC hδ hL0 _ _) le_rfl
  · have hfun : (fun ts k => VineEst.selTreeRow P.L P.γ P.δ h RD hG layer hLayer (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).1
        (ts 0) (ts 1) k) = fun (ts : Fin 2 → ℝ) k =>
          KTstar P.L P.γ P.δ h (Famb.VineEstS3.rowTreeLGΓ hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k := by
      funext ts k
      unfold VineEst.selTreeRow
      rcases not_and_or.mp hc with hw' | hg0
      · exact VineEst.KTsel_of_weighted_eq_false (by simpa using hw') _ _ _ _ _ _ _ _ _ _
      · exact VineEst.KTsel_of_incoh_eq_zero (not_not.mp hg0) _ _ _ _ _ _ _ _ _
    rw [hfun]
    exact Famb.VineEstS5C.treeRow_leaf_leΓ W hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hlay v hel

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W2 MeasureTheory
open scoped ENNReal
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable {hM9 : Famb.NormalChartSupply γF} {B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n} {RD : ReconstructionData G} {hG : G.IsPlain}
  {layer : GNode (RD.forest hG) → ℕ} {hLayer : IsLayering (RD.garden hG) layer}
variable {P : WTParams} {p : ℕ}

/-- **`hres` of the engine for selected rows** (main's `W2.natRows_res`, every selector). -/
theorem natRows_resSΓ {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) {p : ℕ} (hp : p < P.D) (hsel : SelOK P p) {h : ℕ → Mom P.d → ℝ}
    {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B) P.d)
    (hqW : W.q = Famb.VineEstS2.assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqoW : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
    (hel : ∀ v, Famb.VineEstS3.CoupleEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
      Famb.VineEstS3.TreeEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v)
    (ρ : VineEstS3.Eng.Row (Famb.VineEstS2.sourceSumintDatumΓ hM9 B hG W)) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (VineEstS3.Eng.rowOrder (Famb.VineEstS2.sourceSumintDatumΓ hM9 B hG W) ρ)
      (Famb.VineEstS3.rowBxΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ) Set.univ
      ((Famb.VineEstS3.assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ) <
      ENNReal.ofReal (2 * Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) := by
  have hL0 : 0 < P.L := by linarith
  rcases ρ with v | v
  · have h1 := coupleRow_leaf_leSΓ W hgate hinc hsel hqW hqoW hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).1
    have hx : 0 < Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inl v) :=
      mul_pos (rowB_pos hC hδ hL0 _ _) (Famb.VineEstS5C.rowCostH_posΓ hBpos hlay W _)
    refine h1.trans_lt ?_
    change ENNReal.ofReal (Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inl v)) < _
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  · have h1 := treeRow_leaf_leSΓ W hgate hinc hsel hqW hqoW hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).2
    have hx : 0 < Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inr v) :=
      mul_pos (rowB_pos hC hδ hL0 _ _) (Famb.VineEstS5C.rowCostH_posΓ hBpos hlay W _)
    refine h1.trans_lt ?_
    change ENNReal.ofReal (Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inr v)) < _
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W2 MeasureTheory
open scoped ENNReal
variable {γF : ℝ}

/-- **A selected row of the engine datum as a `RowData`, with the leaf-cost bound** (main's `W2.natRowH`, every
selector; the selector is bound after the constant). -/
theorem natRowHSΓ (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {u : Unit} [_I : VineEst.RowSel u] (P : WTParams), P.d = d → P.η = η →
      ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ},
      ∀ {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
      (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
      (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
      (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (hp : p < P.D) (hsel : SelOK P p) (hB : ProfileBound P h Bh p)
      (hBpos : ∀ r ≤ p, 0 < Bh r)
      (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
      (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B) P.d)
      (hqW : W.q = Famb.VineEstS2.assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
      (hqoW : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
      (hel : ∀ v, Famb.VineEstS3.CoupleEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
        Famb.VineEstS3.TreeEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v)
      (hqq : ∀ v, (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
        (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1)
      (wN wDec : ℕ) (hwN : wN + 1 = 30 * P.d) (hwDec : wDec = 30 * P.d)
      (bk : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B).I → Fin 4)
      (cons : Finset ((Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar × (Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar)) (g g' : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → ℕ)
      (ρ : WaveTurbulence.VineEstS3Par.Eng.Row (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g'))
      (slot : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g')),
      ∃ Rr : RowData (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ,
        (∀ cl : Fin 3 → ℝ, ![cl 0, cl 1] ∈ Famb.VineEstS3.rowBxΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ → ∀ r k,
          Rr.W cl r k = (Famb.VineEstS3.assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ ![cl 0, cl 1] k) ∧
        (∀ i, Rr.slot i = slot i) ∧
        Rr.b ≤ C * ENNReal.ofReal (2 * Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) ∧
        Rr.Ae (Famb.VineEstS2.assemblyShape_I_posΓ hM9 B) ∧ (∀ cl r k, Rr.W cl r k = ∑' m, Rr.c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl) := by
  obtain ⟨C, hC0, hCall⟩ := natRowData d η hd
  refine ⟨C, hC0, fun {u} _I P hPd hPη {w G U a b R n} {h Bh p} hgate hinc hη6 hη2 hC hδ hL hw hp hsel hB hBpos hM9 B RD hG
    layer hLayer hlay W hqW hqoW hel hqq wN wDec hwN hwDec bk cons g g' ρ slot => ?_⟩
  subst hPd hPη
  have hres := natRows_resSΓ hgate hinc hd hη6 hη2 hC hδ hL hw hp hsel hB hBpos hM9 B RD hG layer hLayer hlay W hqW hqoW
    hel ρ
  have hord : VineEstS3.Eng.rowOrder (Famb.VineEstS2.sourceSumintDatumΓ hM9 B hG W) ρ =
      WaveTurbulence.VineEstS3Par.Eng.rowOrder (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') ρ := by
    rcases ρ with v | v
    · simp [VineEstS3.Eng.rowOrder, WaveTurbulence.VineEstS3Par.Eng.rowOrder, hwDec]
      rfl
    · rfl
  rw [hord] at hres
  exact hCall (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') (Famb.VineEstS2.assemblyShape_I_posΓ hM9 B) hwN hwDec ρ slot _ _
    ((Famb.VineEstS3.assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ) _ ENNReal.ofReal_ne_top
    (Famb.VineEstS3.rowBx_subset_cellΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ)
    (Famb.VineEstS3.rowBx_closureΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h hqq ρ)
    (fun k => Famb.VineEstS5C.rows_continuousHΓ hB hd hL hlay W ρ k) hres

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
open scoped ENNReal
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal
open WaveTurbulence.VineEstS5C.P4.W2
variable {γF : ℝ}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **All native rows as `RowData`.** -/
theorem natRows_familySΓ (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {u : Unit} [_I : VineEst.RowSel u] (P : WTParams), P.d = d → P.η = η →
      ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ},
      ∀ {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
      (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
      (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
      (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (hp : p < P.D) (hsel : SelOK P p) (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
      (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
      (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B) P.d)
      (hqW : W.q = Famb.VineEstS2.assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
      (hqoW : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
      (hel : ∀ v, Famb.VineEstS3.CoupleEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
        Famb.VineEstS3.TreeEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v)
      (hqq : ∀ v, (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
        (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1)
      (wN wDec : ℕ) (hwN : wN + 1 = 30 * P.d) (hwDec : wDec = 30 * P.d)
      (bk : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B).I → Fin 4)
      (cons : Finset ((Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar × (Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar)) (g g' : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → ℕ),
      ∃ Rw : ∀ ρ : WaveTurbulence.VineEstS3Par.Eng.Row (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g'),
          RowData (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ,
        (∀ ρ (cl : Fin 3 → ℝ), ![cl 0, cl 1] ∈ Famb.VineEstS3.rowBxΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ → ∀ r k,
          (Rw ρ).W cl r k = (Famb.VineEstS3.assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ ![cl 0, cl 1] k) ∧
        (∀ ρ i, (Rw ρ).slot i = Famb.VineEstS5C.P4.W2.natSlotΓ hM9 B hG ρ i) ∧
        (∀ ρ, (Rw ρ).b ≤ C * ENNReal.ofReal (2 * Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ)) ∧
        (∀ ρ, (Rw ρ).Ae (Famb.VineEstS2.assemblyShape_I_posΓ hM9 B)) ∧
        (∀ ρ cl r k, (Rw ρ).W cl r k = ∑' m, (Rw ρ).c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl) := by
  obtain ⟨C, hC0, hCall⟩ := natRowHSΓ d η hd
  refine ⟨C, hC0, fun {u} _I P hPd hPη {w G U a b R n} {h Bh p} hgate hinc hη6 hη2 hC hδ hL hw hp hsel hB hBpos hM9 B RD hG layer hLayer hlay W hqW hqoW hel hqq wN wDec hwN hwDec
    bk cons g g' => ?_⟩
  have := fun ρ => hCall P hPd hPη hgate hinc hη6 hη2 hC hδ hL hw hp hsel hB hBpos hM9 B RD hG layer hLayer hlay W hqW hqoW hel hqq wN wDec hwN hwDec
    bk cons g g' ρ (Famb.VineEstS5C.P4.W2.natSlotΓ hM9 B hG ρ)
  choose Rw hW hS hb hAe hWs using this
  exact ⟨Rw, hW, fun ρ i => hS ρ i, hb, hAe, hWs⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
open scoped ENNReal
open WaveTurbulence.VineEstS5C.P4.W2
variable {γF : ℝ}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The body of `Famb.VineEstS5C.P4.W2.termCertWG_recΓ` for the constant `C` (all the data of the chain, the families and the records are bound inside). -/
def TermRecBodySΓ {A : ℝ} (d : ℕ) (η : ℝ) (C : ℝ≥0∞) : Prop :=
    ∀ {u : Unit} [_I : VineEst.RowSel u] (P : WTParams), P.d = d → P.η = η →
      ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}, ∀ (Z0 : AmbP A P) (hA : 6561 ≤ A)
      (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (hC1 : 1 ≤ P.C₁) (hL1 : 1 ≤ P.L)
      (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (hηγ : P.η ≤ P.γ) {p : ℕ} (hp : p < P.D) (hsel : SelOK P p) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
      (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
      (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
      (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hl1 : clLocalOrder1 R ≤ P.N 1 ^ 4)
      (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (hcoh : Famb.VineEstS3.RowCoherentΓ hM9 B RD hG layer hLayer
        (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
        P.L P.γ P.δ h p)
      (ψ0 : PsiT G P.d) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop) (recs : List (ExcRec G P.d))
      (hNE : RowFormNE RD hG P.L P.γ P.δ h layer hLayer R wBar ψ0 Dm (pexOf recs) (bexOf recs) (xqOf recs))
      (hDm : ∀ t u, u a = t 0 → (Dm t u ↔ DomX R (fun v => layer (RD.coreBranch hG v).toNode) (bexOf recs) (t 0) (t 1) (t 2) u))
      (hnp : (recs.map ExcRec.p0).Nodup) (hnb : (recs.map ExcRec.bj).Nodup)
      (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (hbjI : ∀ r ∈ recs, r.bj ∈ clInteriorBranches R)
      (hblkinj : ∀ r ∈ recs, ∀ r' ∈ recs, r.blk = r'.blk → r = r')
      (blkOf : ∀ r (hr : r ∈ recs), (Famb.VineEstS3.assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩).1.val = r.blk)
      (hbjl : ∀ r ∈ recs, ∀ i : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B).I, r.blk = i.val →
        r.bj = (Famb.VineEstS2.assemblyClockAtomEquivΓ hM9 B (.inl ⟨i, 0⟩)).1)
      (hnorR : ∀ r ∈ recs, ∀ i : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B).I, r.blk = i.val → (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false)
      (kd : ExcRec G P.d → ℕ) (zc : ExcRec G P.d → Prop)
      (addr : ExcRec G P.d → Finset ((Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar × (Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar)) (bnd : ExcRec G P.d → ℝ≥0∞)
      (hspec : ∀ r (hr : r ∈ recs),
        Famb.VineEstS5C.P4.W2.RecSpecΓ (P := P) (κ0 := kparOf P.L P.γ P.δ h wBar) B RD hG layer hM9 (ne_of_gt (lt_of_lt_of_le one_pos hL1)) r (hreg r hr) (hbjI r hr)
          (kd r) (zc r) (addr r) (bnd r))
      (hfreeR : ∀ i : Fin n, (∀ r ∈ recs, r.blk ≠ i.val) → (Famb.VineEstS2.assemblyPieceAtΓ B i).label.IsBad = true → ¬ Famb.VineEstS3.AClauseΓ hM9 B RD hG layer i →
        ∃ v : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx, v.1 = i ∧
          1 ≤ max (Famb.VineEstS3.rowCoupleGΓ hM9 B RD hG layer hLayer v) (Famb.VineEstS3.rowTreeGΓ hM9 B RD hG layer hLayer v))
      (Bx : Set (Fin 3 → ℝ)) (K : Set (Fin 4 → Mom P.d))
      (hBx : Bx ⊆ WaveTurbulence.VineEstS3Par.Eng.outBox
        (Famb.VineEstS5C.P4.W2.natEngΓ hM9 B RD hG layer hLayer (qOutOf RD hG layer a b R) centre wBar lam))
      (hext : ∀ tt ∈ Bx, ((layC RD hG layer a : ℕ) : ℝ) < tt 0 ∧ tt 0 < (layC RD hG layer a : ℕ) + 1)
      (hK : K = WaveTurbulence.VineEstS3Par.Eng.outSet
        (Famb.VineEstS5C.P4.W2.natEngΓ hM9 B RD hG layer hLayer (qOutOf RD hG layer a b R) centre wBar lam) P.L P.γ P.η),
      ∃ q : ℝ≥0∞, (∀ β', q ≤ β' → Famb.VineEstS5C.P4.W2.TermCertWGΓ (A := A) B hG (kparOf P.L P.γ P.δ h wBar) R (modPsi b lam ψ0) Bx K β') ∧
        ∃ Rb : Row (Famb.VineEstS5C.P4.W2.recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) → ℝ≥0∞,
          q ≤ certBeta P (Famb.VineEstS5C.P4.W2.recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) ((3 : ℝ) ^ (clLocalOrder1 R + 1)) Rb ∧
          (∀ ρ, (∀ r (hr : r ∈ recs), ρ ≠ Sum.inl (Famb.VineEstS3.assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩) ∧
              ρ ≠ Sum.inr (Famb.VineEstS3.assemblyBranchBijΓ hM9 B ⟨r.bj, hbjI r hr⟩)) →
            Rb ρ = C * ENNReal.ofReal (2 * Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh
              (Famb.VineEstS5C.P4.W2.recWΓ hM9 B RD hG layer hLayer recs kd zc centre wBar lam) ρ)) ∧
          ∀ r (hr : r ∈ recs), Rb (Sum.inl (Famb.VineEstS3.assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩)) = bnd r ∧
            Rb (Sum.inr (Famb.VineEstS3.assemblyBranchBijΓ hM9 B ⟨r.bj, hbjI r hr⟩)) = 1

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
open scoped ENNReal
open WaveTurbulence.VineEstS5C.P4.W2
variable {γF : ℝ}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The certificate of a term with records** (see the module docstring). -/
theorem termCertWG_recSΓ {A : ℝ} (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, 1 ≤ C ∧ C ≠ ⊤ ∧ TermRecBodySΓ (γF := γF) (A := A) d η C := by
  classical
  obtain ⟨C0, hC00, hall⟩ := natRows_familySΓ d η hd
  refine ⟨C0 + 1, le_add_self, ENNReal.add_ne_top.2 ⟨hC00, ENNReal.one_ne_top⟩, ?_⟩
  unfold TermRecBodySΓ
  intro u _I P hPd hPη w G U a b R n Z0 hA hgate hinc hC1 hL1 hw hηγ p hp hsel h Bh hB hBpos hM9 B RD hG layer hLayer hlay hord hl1
    centre wBar lam hcoh ψ0 Dm recs hNE hDm hnp hnb hreg hbjI hblkinj blkOf hbjl hnorR kd zc addr bnd hspec hfreeR Bx K hBx hext hK
  have hd' : 1 ≤ P.d := hPd ▸ hd
  have hL0 : 0 < P.L := by linarith
  set C : ℝ≥0∞ := C0 + 1 with hCdef
  set qOut := qOutOf RD hG layer a b R with hqOut
  set bk := Famb.VineEstS5C.P4.W2.recBkΓ B RD hG layer hM9 recs kd zc with hbk
  set W := Famb.VineEstS5C.P4.W2.recWΓ hM9 B RD hG layer hLayer recs kd zc centre wBar lam with hW
  set wN := 30 * P.d - 1 with hwNd
  set wDec := 30 * P.d with hwDecd
  set cons := Famb.VineEstS5C.P4.W2.consXΓ hM9 B (layC RD hG layer) (bexOf recs) (Famb.VineEstS5C.P4.W2.recAddΓ B hM9 recs zc addr) with hcons
  set g := Famb.VineEstS5C.P4.W2.recGΓ B hM9 hG recs kd (Famb.VineEstS3.rowCoupleGΓ hM9 B RD hG layer hLayer) with hg
  set g' := Famb.VineEstS3.rowTreeGΓ hM9 B RD hG layer hLayer with hg'
  have hI := Famb.VineEstS2.assemblyShape_I_posΓ hM9 B
  -- record bookkeeping
  obtain ⟨vpf, vbf, hvpf, hvbf⟩ := Famb.VineEstS5C.P4.W2.exists_row_mapsΓ hM9 B hG recs hreg hbjI
  have hvp : ∀ r ∈ recs, (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG (vpf r)).1 = r.p0 := fun r hr => by
    rw [hvpf r hr, Famb.VineEstS4.assemblyPairOf_bijΓ hM9 B hG]
  have hvb : ∀ r ∈ recs, (Famb.VineEstS2.assemblyBranchOfΓ hM9 B (vbf r)).1 = r.bj := fun r hr => by
    rw [hvbf r hr, Famb.VineEstS4.assemblyBranchOf_bijΓ hM9 B]
  have hblk : ∀ r ∈ recs, ((vpf r).1 : ℕ) = r.blk := fun r hr => by rw [hvpf r hr]; exact blkOf r hr
  -- eligibility of the native rows
  have hel : ∀ v, Famb.VineEstS3.CoupleEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
      Famb.VineEstS3.TreeEligibleΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v := fun v =>
    Famb.VineEstS3.eligible_ofΓ hM9 B RD hG layer hLayer W rfl rfl P.L P.γ P.δ h (P.N (p + 1) ^ 4) p hlay
      (Famb.VineEstS4.rowSizes_of_orderΓ hM9 B RD hG hord) hcoh v
  have hqq : ∀ v, (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
      (Famb.VineEstS3.rowQΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1 := fun v => (hel v).2.1
  have hη6 : 6 * P.η ^ 6 ≤ P.η := Z0.hθη
  obtain ⟨Rw0, hRW0, hRS0, hRb0, hAe0, hWs0⟩ := hall P hPd hPη hgate hinc hη6 Z0.hη1 hC1 Z0.hδ hL1 hw hp hsel hB hBpos hM9 B RD hG layer hLayer hlay W rfl rfl
    hel hqq wN wDec (by omega) (by omega) bk cons g g'
  obtain ⟨Mx, hmass, hMx⟩ := Famb.VineEstS5C.P4.W2.exists_mix_nativeΓ hM9 B hG W hL0.ne' wBar
  have hq : ∀ v, W.q v + 1 ≤ P.D := fun v => Nat.succ_le_of_lt (lt_of_le_of_lt (hlay _) hp)
  have hqo : ∀ c, W.qOut c + 1 ≤ P.D := by
    intro c
    refine Nat.succ_le_of_lt (lt_of_le_of_lt ?_ hp)
    fin_cases c <;> simp only [W, Famb.VineEstS5C.P4.W2.recWΓ, Famb.VineEstS5C.P4.W2.termWΓ, Famb.VineEstS3.step3WΓ, hqOut, qOutOf] <;> exact hlay _
  have hS := Famb.VineEstS5C.P4.W2.structAdm_engDatumΓ hM9 B hG W (L := P.L) (γ := P.γ) (η := P.η) hA hq hqo wN wDec (by omega) (by omega) bk cons g g'
  have hkd : ∀ r ∈ recs, kd r ≤ 3 := fun r hr => (hspec r hr).1
  have hm2 : ∀ r ∈ recs, kd r = 2 → ∀ i : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B).I, r.blk = i.val → 0 < (Famb.VineEstS2.assemblyShapeΓ hM9 B).m i := by
    intro r hr hk2 i hi
    have hi' : (Famb.VineEstS3.assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩).1 = i := Fin.ext ((blkOf r hr).trans hi)
    rw [← hi']
    exact (hspec r hr).2.1 hk2
  have hbad : BadClauseP (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') := by
    refine Famb.VineEstS5C.P4.W2.badClauseP_recΓ B RD hG layer hLayer hM9 hG W wN wDec recs kd zc addr hblkinj hkd hm2
      (fun r hr => ?_) (fun r hr i hi => ?_) (fun r hr hk3 => ?_) hfreeR
    · exact ⟨(vpf r).1, (hblk r hr).symm, hbjl r hr _ (hblk r hr).symm⟩
    · have hi' : (Famb.VineEstS3.assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩).1 = i := Fin.ext ((blkOf r hr).trans hi)
      rw [← hi']
      exact (hspec r hr).2.2.1
    · exact ⟨vpf r, hvp r hr, hblk r hr⟩
  have hgap : ∀ i (hh : (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g').S.nor i = false ∧
      (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g').badKind i = 2 ∧ 0 < (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g').S.m i),
      |(((Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g').q (.inl ⟨i, ⟨1, by omega⟩⟩) : ℕ) : ℝ) -
        (((Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g').q (.inr (.inl ⟨i, ⟨0, hh.2.2⟩⟩)) : ℕ) : ℝ)| ≤ (P.D : ℝ) :=
    fun i hh => abs_sub_nat_leS _ _ P.D (Nat.le_of_succ_le (hq _)) (Nat.le_of_succ_le (hq _))
  let Z := Famb.VineEstS5C.P4.W2.ambW_engDatumΓ Z0 hM9 B hG W wN wDec bk cons g g' hS hbad Mx (P.D : ℝ) (Nat.cast_nonneg _) hgap (by omega)
    (by rw [Famb.VineEstS2.assemblyShape_MΓ]; exact hl1)
  have hleafmem : ∀ tt ∈ Bx, WaveTurbulence.VineEstS3.leafT qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B (Famb.VineEstS5C.LvlΓ.top B)) (Famb.VineEstS5C.P4.W2.LeafNegΓ B (Famb.VineEstS5C.LvlΓ.top B)) tt ∈
      WaveTurbulence.VineEstS3.Eng.outBox (Famb.VineEstS2.sourceSumintDatumΓ hM9 B hG W) := fun tt htt =>
    leafT_mem_boxQ qOut _ _ (hBx htt)
  -- the effective output times
  set Bx' : Set (Fin 3 → ℝ) := (fun tt => WaveTurbulence.VineEstS3.leafT qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B (Famb.VineEstS5C.LvlΓ.top B)) (Famb.VineEstS5C.P4.W2.LeafNegΓ B (Famb.VineEstS5C.LvlΓ.top B)) tt) '' Bx
    with hBx'def
  have hBx'sub : Bx' ⊆ outBox (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') := by
    rintro _ ⟨tt, htt, rfl⟩
    exact leafT_mem_boxQ qOut _ _ (hBx htt)
  have hext' : ∀ tt ∈ Bx', ((layC RD hG layer a : ℕ) : ℝ) < tt 0 ∧ tt 0 < (layC RD hG layer a : ℕ) + 1 := by
    rintro _ ⟨tt, htt, rfl⟩
    beta_reduce
    rw [WaveTurbulence.VineEstS3.leafT_zero qOut _ _ tt]
    exact hext tt htt
  have hrc := fun r (hr : r ∈ recs) => (hspec r hr).2.2.2.2 W wN wDec (by omega) (by omega) bk (bexOf recs) (Famb.VineEstS5C.P4.W2.recAddΓ B hM9 recs zc addr) g g'
    rfl Bx' hBx'sub hext' (fun hz => Famb.VineEstS5C.P4.W2.addr_subset_recAddΓ B hM9 recs zc addr hr hz)
  choose! ε Xr hεabs hPU hzero hlink using hrc
  have hinjp : ∀ k ∈ recs.toFinset, ∀ k' ∈ recs.toFinset, vpf k = vpf k' → k = k' := by
    intro k hk k' hk' hkk
    have h1 : k.p0 = k'.p0 := by
      rw [← hvp k (List.mem_toFinset.mp hk), ← hvp k' (List.mem_toFinset.mp hk'), hkk]
    exact List.inj_on_of_nodup_map hnp (List.mem_toFinset.mp hk) (List.mem_toFinset.mp hk') h1
  have hinjb : ∀ k ∈ recs.toFinset, ∀ k' ∈ recs.toFinset, vbf k = vbf k' → k = k' := by
    intro k hk k' hk' hkk
    have h1 : k.bj = k'.bj := by
      rw [← hvb k (List.mem_toFinset.mp hk), ← hvb k' (List.mem_toFinset.mp hk'), hkk]
    exact List.inj_on_of_nodup_map hnb (List.mem_toFinset.mp hk) (List.mem_toFinset.mp hk') h1
  obtain ⟨Rw', hRw'1, hRw'2⟩ := rows_merge (P := P) hI Rw0 recs.toFinset vpf vbf hinjp hinjb ε
    (fun r => f0Of P.η (vpf r).1 (kd r)) Xr bnd Bx'
    (fun k hk => by
      have := hPU k (List.mem_toFinset.mp hk)
      rwa [← hvpf k (List.mem_toFinset.mp hk), ← hvbf k (List.mem_toFinset.mp hk)] at this)
  have hnonexc : ∀ ρ, Famb.VineEstS5C.P4.W2.NonExcΓ hM9 B hG W wN wDec bk cons g g' (Famb.VineEstS5C.P4.W2.vpSetΓ hM9 B hG recs) (Famb.VineEstS5C.P4.W2.vbSetΓ hM9 B recs) ρ → Rw' ρ = Rw0 ρ := by
    intro ρ hρ
    refine hRw'1 ρ fun k hk => ⟨fun h' => ?_, fun h' => ?_⟩
    · have hk' := List.mem_toFinset.mp hk
      exact hρ.1 (vpf k) h' ((Famb.VineEstS5C.P4.W2.mem_vpSetΓ hM9 B hG recs _).mpr (by rw [hvp k hk']; exact mem_pexOf.mpr ⟨k, hk', rfl⟩))
    · have hk' := List.mem_toFinset.mp hk
      exact hρ.2 (vbf k) h' ((Famb.VineEstS5C.P4.W2.mem_vbSetΓ hM9 B recs _).mpr (by rw [hvb k hk']; exact mem_bexOf.mpr ⟨k, hk', rfl⟩))
  have hRW : ∀ ρ (cl : Fin 3 → ℝ), Famb.VineEstS5C.P4.W2.NonExcΓ hM9 B hG W wN wDec bk cons g g' (Famb.VineEstS5C.P4.W2.vpSetΓ hM9 B hG recs) (Famb.VineEstS5C.P4.W2.vbSetΓ hM9 B recs) ρ →
      ![cl 0, cl 1] ∈ Famb.VineEstS3.rowBxΓ hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ → ∀ r k,
      (Rw' ρ).W cl r k = (Famb.VineEstS3.assemblyClockedSΓ hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ ![cl 0, cl 1] k := by
    intro ρ cl hρ hcl r k
    rw [hnonexc ρ hρ]
    exact hRW0 ρ cl hcl r k
  have hRS : ∀ ρ i, Famb.VineEstS5C.P4.W2.NonExcΓ hM9 B hG W wN wDec bk cons g g' (Famb.VineEstS5C.P4.W2.vpSetΓ hM9 B hG recs) (Famb.VineEstS5C.P4.W2.vbSetΓ hM9 B recs) ρ →
      (Rw' ρ).slot i = Famb.VineEstS5C.P4.W2.natSlotΓ hM9 B hG ρ i := by
    intro ρ i hρ
    rw [hnonexc ρ hρ]
    exact hRS0 ρ i
  have hAe' : ∀ ρ, (Rw' ρ).Ae hI := by
    intro ρ
    by_cases hex : ∃ k ∈ recs.toFinset, ρ = Sum.inl (vpf k) ∨ ρ = Sum.inr (vbf k)
    · obtain ⟨k, hk, hρ | hρ⟩ := hex
      · subst hρ; exact (hRw'2 k hk).1
      · subst hρ; exact (hRw'2 k hk).2.1
    · push_neg at hex
      rw [hRw'1 ρ fun k hk => hex k hk]
      exact hAe0 ρ
  have hWs' : ∀ ρ cl r k, (Rw' ρ).W cl r k = ∑' m, (Rw' ρ).c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl := by
    intro ρ cl r k
    by_cases hex : ∃ k ∈ recs.toFinset, ρ = Sum.inl (vpf k) ∨ ρ = Sum.inr (vbf k)
    · obtain ⟨k', hk, hρ | hρ⟩ := hex
      · subst hρ; exact (hRw'2 k' hk).2.2.1 cl r k
      · subst hρ; exact (hRw'2 k' hk).2.2.2.1 cl r k
    · push_neg at hex
      rw [hRw'1 ρ fun k hk => hex k hk]
      exact hWs0 ρ cl r k
  have hbkr : ∀ r ∈ recs, bk ((vpf r).1) = bkVal (kd r) (zc r) := fun r hr =>
    Famb.VineEstS5C.P4.W2.recBk_of_recΓ B RD hG layer hM9 recs kd zc hblkinj hr _ (hblk r hr).symm
  have hbkn : ∀ i, (∀ r ∈ recs, (vpf r).1 ≠ i) → bk i ≠ 1 ∧ bk i ≠ 2 := by
    intro i hne
    have hn : ∀ r ∈ recs, r.blk ≠ i.val := fun r hr h' => hne r hr (Fin.ext ((hblk r hr).trans h'))
    rw [hbk, Famb.VineEstS5C.P4.W2.recBk_of_notΓ B RD hG layer hM9 recs kd zc i hn]
    rcases Famb.VineEstS3.canonBadKind_casesΓ hM9 B RD hG layer i with h' | h' <;> rw [h'] <;> decide
  have hLP : Famb.VineEstS5C.P4.W2.LeafPosΓ B (Famb.VineEstS5C.LvlΓ.top B) ↔ (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching := by
    unfold Famb.VineEstS5C.P4.W2.LeafPosΓ; rw [Famb.VineEstS5C.P4.W2.top_region_eqΓ B]; exact Iff.rfl
  have hLN : Famb.VineEstS5C.P4.W2.LeafNegΓ B (Famb.VineEstS5C.LvlΓ.top B) ↔ (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching := by
    unfold Famb.VineEstS5C.P4.W2.LeafNegΓ; rw [Famb.VineEstS5C.P4.W2.top_region_eqΓ B]; exact Iff.rfl
  have hD : ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign (Famb.VineEstS5C.LvlΓ.top B).c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign (Famb.VineEstS5C.LvlΓ.top B).c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') P.L P.γ P.η →
      Famb.VineEstS5C.P4.W2.FreeDictΓ hM9 B hG W hL0.ne' P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B (Famb.VineEstS5C.LvlΓ.top B)) (Famb.VineEstS5C.P4.W2.LeafNegΓ B (Famb.VineEstS5C.LvlΓ.top B)) tt)
        (modPsi b lam ψ0) wN wDec bk cons g g' Mx (allCR Rw') := by
    intro tt0 htt0 β hβ hout
    have hmemB' : WaveTurbulence.VineEstS3.leafT qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B (Famb.VineEstS5C.LvlΓ.top B)) (Famb.VineEstS5C.P4.W2.LeafNegΓ B (Famb.VineEstS5C.LvlΓ.top B)) tt0 ∈ Bx' := ⟨tt0, htt0, rfl⟩
    have hr1 : ‖sumintBoundary (G.sign a.toNode) (fun j => wBar + latticePoint P.L (β j)) 0 -
        sumintBoundary (G.sign a.toNode) (fun j => wBar + latticePoint P.L (β j)) 1‖ ≤ 1 := by
      refine hout.2.2.2.trans ?_
      exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
    refine Famb.VineEstS5C.P4.W2.freeDict_recΓ hM9 B RD hG W hL0.ne' P.γ P.δ P.η h layer hLayer wBar β hβ _ (hleafmem tt0 htt0) (modPsi b lam ψ0) ψ0 lam
      (fun x t u => rfl) Dm (pexOf recs) (bexOf recs) (xqOf recs) hNE hDm wN wDec bk (Famb.VineEstS5C.P4.W2.recAddΓ B hM9 recs zc addr) g g' Mx Rw'
      (Famb.VineEstS5C.P4.W2.vpSetΓ hM9 B hG recs) (Famb.VineEstS5C.P4.W2.vbSetΓ hM9 B recs) (Famb.VineEstS5C.P4.W2.mem_vpSetΓ hM9 B hG recs) (Famb.VineEstS5C.P4.W2.mem_vbSetΓ hM9 B recs) hRW hRS (fun v => rfl)
      (fun x => hMx β hβ x) rfl ?_ ?_ ?_ ?_
    · by_cases hh : Famb.VineEstS5C.P4.W2.LeafPosΓ B (Famb.VineEstS5C.LvlΓ.top B)
      · refine Or.inr ?_
        rw [WaveTurbulence.VineEstS3.leafT_one]
        simp only [hh, if_true]
        exact Famb.VineEstS3.qOutOf_one_leΓ hM9 B RD hG layer hLayer hI
      · exact Or.inl (not_not.mp (mt hLP.mpr hh))
    · by_cases hh : Famb.VineEstS5C.P4.W2.LeafNegΓ B (Famb.VineEstS5C.LvlΓ.top B)
      · refine Or.inr ?_
        rw [WaveTurbulence.VineEstS3.leafT_two]
        simp only [hh, if_true]
        exact Famb.VineEstS3.qOutOf_two_leΓ hM9 B RD hG layer hLayer hI
      · exact Or.inl (not_not.mp (mt hLN.mpr hh))
    · intro x
      exact (Famb.VineEstS5C.P4.W2.hcontract_of_recordsΓ hM9 B recs hnp hreg zc addr (fun r hr => (hspec r hr).2.2.2.1) _
        (clExtendIndices R ((Famb.VineEstS2.clNormalizedChainEquivΓ hL0.ne' B wBar β hβ hM9).symm x).1)
        (fun τ p => qRow RD hG P.L P.γ P.δ h layer hLayer wBar _ (clExtendIndices R ((Famb.VineEstS2.clNormalizedChainEquivΓ hL0.ne' B wBar β hβ hM9).symm x).1)
          (clLocalClock R _ (Famb.VineEstS2.assemblyClockEquivΓ hM9 B τ)) p)
        (fun τ v => tRow RD hG P.L P.γ P.δ h layer hLayer wBar _ (clExtendIndices R ((Famb.VineEstS2.clNormalizedChainEquivΓ hL0.ne' B wBar β hβ hM9).symm x).1)
          (clLocalClock R _ (Famb.VineEstS2.assemblyClockEquivΓ hM9 B τ)) v)).mono (fun τ h' _ => h')
    · intro x
      refine Famb.VineEstS5C.P4.W2.hX_recΓ hM9 B hG W hL0.ne' P.η wBar β hβ _ x wN wDec bk cons g g' Rw' Bx' hmemB' hr1 recs hnp hnb hreg kd zc
        (fun r => (vpf r).1) (fun r hr r' hr' h' => hblkinj r hr r' hr' (by rw [← hblk r hr, ← hblk r' hr', h'])) hkd hbkr hbkn
        (fun r hr => hnorR r hr _ (hblk r hr).symm) vpf vbf hvp hvb (fun r hr => ⟨ε r, Xr r, bnd r, hRw'2 r (List.mem_toFinset.mpr hr), hzero r hr, ?_⟩)
      intro tt τ
      have := hlink r hr β hβ x tt τ
      rwa [← hvpf r hr, ← hvbf r hr] at this
  have hind' : ∀ (t : Fin 3 → ℝ) (β'' : Fin 4 → Mom P.d) (κ : CLLocalDecoration R P.L W.wBar β'') (u : GBranch G.tree → ℝ),
      u (Famb.VineEstS5C.LvlΓ.top B).c.a = t 0 → modPsi b lam ψ0 (clExtendIndices R κ.1) t u = modPsi b lam ψ0 (clExtendIndices R κ.1)
        (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B (Famb.VineEstS5C.LvlΓ.top B)) (Famb.VineEstS5C.P4.W2.LeafNegΓ B (Famb.VineEstS5C.LvlΓ.top B)) t) u := by
    intro t β'' κ u hu
    show Complex.exp _ * ψ0 _ t u = Complex.exp _ * ψ0 _ _ u
    congr 1
    refine hind_exc RD hG P.L P.γ P.δ h layer hLayer wBar ψ0 Dm recs hNE hDm t _
      (WaveTurbulence.VineEstS3.leafT_zero qOut _ _ t).symm ?_ ?_ β'' κ u hu
    · by_cases hh : Famb.VineEstS5C.P4.W2.LeafPosΓ B (Famb.VineEstS5C.LvlΓ.top B)
      · exact Or.inl (hLP.mp hh)
      · exact Or.inr (by rw [WaveTurbulence.VineEstS3.leafT_one]; simp [hh])
    · by_cases hh : Famb.VineEstS5C.P4.W2.LeafNegΓ B (Famb.VineEstS5C.LvlΓ.top B)
      · exact Or.inl (hLN.mp hh)
      · exact Or.inr (by rw [WaveTurbulence.VineEstS3.leafT_two]; simp [hh])
  -- the bound on the product of the row sizes
  let e1 : ExcRec G P.d → Row (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') := fun k => Sum.inl (vpf k)
  let e2 : ExcRec G P.d → Row (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') := fun k => Sum.inr (vbf k)
  let Rb : Row (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g') → ℝ≥0∞ := fun ρ =>
    if h1 : ∃ k ∈ recs.toFinset, ρ = e1 k then bnd h1.choose
    else if ∃ k ∈ recs.toFinset, ρ = e2 k then 1
    else C * ENNReal.ofReal (2 * Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ)
  have hRbl : ∀ k ∈ recs.toFinset, Rb (e1 k) = bnd k := by
    intro k hk
    have h1 : ∃ k' ∈ recs.toFinset, e1 k = e1 k' := ⟨k, hk, rfl⟩
    dsimp only [Rb]
    rw [dif_pos h1]
    have := hinjp _ h1.choose_spec.1 k hk (Sum.inl.inj h1.choose_spec.2).symm
    rw [this]
  have hRbr : ∀ k ∈ recs.toFinset, Rb (e2 k) = 1 := by
    intro k hk
    have h1 : ¬ ∃ k' ∈ recs.toFinset, e2 k = e1 k' := by
      rintro ⟨k', -, h'⟩; exact Sum.inr_ne_inl h'
    have h2 : ∃ k' ∈ recs.toFinset, e2 k = e2 k' := ⟨k, hk, rfl⟩
    dsimp only [Rb]
    rw [dif_neg h1, if_pos h2]
  have hRbn : ∀ ρ, (∀ k ∈ recs.toFinset, ρ ≠ e1 k ∧ ρ ≠ e2 k) →
      Rb ρ = C * ENNReal.ofReal (2 * Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) := by
    intro ρ hρ
    have h1 : ¬ ∃ k' ∈ recs.toFinset, ρ = e1 k' := by
      rintro ⟨k', hk', h'⟩; exact (hρ k' hk').1 h'
    have h2 : ¬ ∃ k' ∈ recs.toFinset, ρ = e2 k' := by
      rintro ⟨k', hk', h'⟩; exact (hρ k' hk').2 h'
    dsimp only [Rb]
    rw [dif_neg h1, if_neg h2]
  have hprod : ∏ ρ, (Rw' ρ).b ≤ ∏ ρ, Rb ρ := by
    have h1 := prod_split_leS (fun ρ => (Rw' ρ).b) Rb recs.toFinset e1 e2
      (fun k hk k' hk' h' => hinjp k hk k' hk' (Sum.inl.inj h')) (fun k hk k' hk' h' => hinjb k hk k' hk' (Sum.inr.inj h')) 
      (fun k _ k' _ => Sum.inl_ne_inr) bnd
      (fun ρ hρ => by
        have hcond : ∀ k ∈ recs.toFinset, ρ ≠ e1 k ∧ ρ ≠ e2 k := fun k hk =>
          ⟨fun h' => hρ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hk, h'.symm⟩)),
           fun h' => hρ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, h'.symm⟩))⟩
        rw [hRw'1 ρ hcond, hRbn ρ hcond]
        exact (hRb0 ρ).trans (mul_le_mul' (le_self_add) le_rfl))
      (fun k hk => (hRw'2 k hk).2.2.2.2.1)
    have hexc : ∏ ρ ∈ recs.toFinset.image e1 ∪
        recs.toFinset.image e2, Rb ρ = ∏ k ∈ recs.toFinset, bnd k := by
      have hd : Disjoint (recs.toFinset.image e1)
          (recs.toFinset.image e2) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨k', -, h'⟩ := Finset.mem_image.mp hx'
        exact Sum.inr_ne_inl h'
      have hI1 : Set.InjOn e1 ↑recs.toFinset :=
        fun k hk k' hk' h' => hinjp k hk k' hk' (Sum.inl.inj h')
      have hI2 : Set.InjOn e2 ↑recs.toFinset :=
        fun k hk k' hk' h' => hinjb k hk k' hk' (Sum.inr.inj h')
      rw [Finset.prod_union hd, Finset.prod_image hI1, Finset.prod_image hI2,
        Finset.prod_congr rfl hRbl, Finset.prod_congr rfl hRbr, Finset.prod_const_one, mul_one]
    refine h1.trans (le_of_eq ?_)
    rw [← hexc]
    exact Finset.prod_sdiff (Finset.subset_univ _)
  refine ⟨Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 * (Z.pre * ∏ ρ, (Rw' ρ).b),
    fun β' hβ' => ⟨n, hM9, B, W, wN, wDec, bk, cons, g, g', Z, Rw', hL0.ne', hAe', hWs', rfl, hBx, hK, hind', hD, hβ'⟩,
    Rb, ?_, ?_, ?_⟩
  · rw [← hmass]
    exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hprod)
  · intro ρ hρ
    refine hRbn ρ fun k hk => ?_
    have hk' := List.mem_toFinset.mp hk
    constructor
    · show ρ ≠ Sum.inl (vpf k)
      rw [hvpf k hk']; exact (hρ k hk').1
    · show ρ ≠ Sum.inr (vbf k)
      rw [hvbf k hk']; exact (hρ k hk').2
  · intro r hr
    refine ⟨?_, ?_⟩
    · rw [← hvpf r hr]; exact hRbl r (List.mem_toFinset.mpr hr)
    · rw [← hvbf r hr]; exact hRbr r (List.mem_toFinset.mpr hr)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open VineParamContract
open scoped ENNReal
open WaveTurbulence.VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.W2
open Set
variable {γF : ℝ}
variable {kind : Bool}
variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]

/-- **The uniform per-term certificate at one engine parameter, for every selector** (main's `Famb.VineEstS5C.P4.Final.UniformTermCertAtKΓ`
with the weighted-selector hypothesis `hsel : SelOK Pe p`). -/
def UniformTermCertAtKSΓ (A : ℝ) (Pe : WTParams) (Km Kr Kb : ℝ) : Prop :=
  ∀ {p : ℕ} (h : ℕ → Mom Pe.d → ℝ) (B₀ : ℝ) (wBar : Mom Pe.d), 0 < B₀ →
    ∀ (E : GateEnv Pe (kparOf Pe.L Pe.γ Pe.δ h wBar) p (fun _ => B₀)) (hinc : IncoherentGateH Pe) (hsel : SelOK Pe p)
      {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    ∀ (hord : (RD.garden hG).order ≤ Pe.N (p + 1) ^ 4), clLocalOrder1 R ≤ Pe.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom Pe.d) (lam : ℝ) (hR : RealityAll),
    Famb.VineEstS3.RowCoherentΓ hM9 B RD hG layer hLayer
      (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.δ h p →
    ∃ β' : ℝ≥0∞,
      (∀ ψ ∈ Famb.VineEstS5C.P4.Bot.LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer
          (Famb.VineEstS5C.P4.bundleFamOfΓ B RD hG layer hLayer hR (Famb.VineEstS5C.P4.W13.sffOfΓ (hprime := hprime) B RD hG layer hLayer E hord))
          (Famb.VineEstS5C.P4.Bot.bundleBotFamOfΓ B RD hG layer hLayer hprime hR (Famb.VineEstS5C.P4.Final.botSffOfΓ B RD hG layer hLayer hprime E hord))
          (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B),
        Famb.VineEstS5C.P4.W2.TermCertWΓ (A := A) B hG (kparOf Pe.L Pe.γ Pe.δ h wBar) (Famb.VineEstS5C.LvlΓ.top B) (modPsi b lam ψ)
          (openTop (WaveTurbulence.VineEstS3.Eng.outBox (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
            (layer (RD.coreBranch hG a).toNode : ℝ))
          (WaveTurbulence.VineEstS3.Eng.outSet (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
            Pe.L Pe.γ Pe.η) β') ∧
      ‖(coupling Pe.d Pe.L Pe.γ Pe.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ * β' ≤
        ENNReal.ofReal ((1 + |lam|) ^ (6 * Pe.η ^ 6) * ((engNs Pe.η Pe.C₁ Km Kr * Real.sqrt Pe.δ) ^ clLocalOrder2 RD hG R *
          (Kb ^ (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card *
          Pe.L ^ (-(Pe.η ^ 8 * ((Famb.VineEstS3.cohmolIndexΓ B RD hG layer +
            (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
            Pe.η ^ 2 * ((Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7)) *
          regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open VineParamContract
open scoped ENNReal
open WaveTurbulence.VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.W2
open Set
variable {γF : ℝ}
variable {kind : Bool}
variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

open Classical in
theorem term_rec_existsSΓ {Pe : WTParams} (hPe : AmbP 6561 Pe) (hL2 : 2 ≤ Pe.L) (hηγ : Pe.η ≤ Pe.γ)
    (hw : 0 ≤ Pe.gamma1 - Real.sqrt Pe.η)
    {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCt : C ≠ ⊤) (hbody : TermRecBodySΓ (γF := γF) (A := 6561) Pe.d Pe.η C)
    {K0 : ℝ≥0∞} (hK0t : K0 ≠ ⊤) (hdisp : DispK01.{0} Pe K0) (hd2 : DispK2.{0} Pe (Pe.D : ℝ) K0)
    (cf Kr Kb Km : ℝ) (hcf : C.toReal ≤ cf) (hKr : cf * 2 * (rowCb Pe * Pe.C₁ ^ 2) ≤ Kr) (hKr1 : 1 ≤ Kr)
    (hKb : (Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η))).toReal * (4 * TR Pe.η ^ 2 * trC (6 * Pe.η ^ 6) ^ 2 / rowCb Pe ^ 2) ≤ Kb) (hKb1 : 1 ≤ Kb)
    (hKm1 : 1 ≤ Km) (hKm : 3 * max (tcSq Pe.η) 1 ≤ Km)
    {p : ℕ} (h : ℕ → Mom Pe.d → ℝ) (B₀ : ℝ) (wBar : Mom Pe.d) (hB₀ : 0 < B₀)
    (E : GateEnv Pe (kparOf Pe.L Pe.γ Pe.δ h wBar) p (fun _ => B₀)) (hinc : IncoherentGateH Pe) (hsel : SelOK Pe p)
    (hprime : IsPrimeGarden G) (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hcan : CanonicalObject p kind (layeredReconstruction RD hG layer hLayer)) (hlay : ∀ x, layer x ≤ p)
    (hord : (RD.garden hG).order ≤ Pe.N (p + 1) ^ 4) (hl1 : clLocalOrder1 R ≤ Pe.N 1 ^ 4)
    (centre : Fin 4 → Mom Pe.d) (lam : ℝ) (hR : RealityAll)
    (hcoh : Famb.VineEstS3.RowCoherentΓ hM9 B RD hG layer hLayer
      (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.δ h p) :
    ∀ ψ ∈ Famb.VineEstS5C.P4.Bot.LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer
          (Famb.VineEstS5C.P4.bundleFamOfΓ B RD hG layer hLayer hR (Famb.VineEstS5C.P4.W13.sffOfΓ (hprime := hprime) B RD hG layer hLayer E hord))
          (Famb.VineEstS5C.P4.Bot.bundleBotFamOfΓ B RD hG layer hLayer hprime hR
            (Famb.VineEstS5C.P4.Final.botSffOfΓ B RD hG layer hLayer hprime E hord))
          (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B),
      ∃ q : ℝ≥0∞, (∀ β', q ≤ β' →
          Famb.VineEstS5C.P4.W2.TermCertWΓ (A := 6561) B hG (kparOf Pe.L Pe.γ Pe.δ h wBar) (Famb.VineEstS5C.LvlΓ.top B) (modPsi b lam ψ)
            (openTop (WaveTurbulence.VineEstS3.Eng.outBox (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer)
              (qOutOf RD hG layer a b R) centre wBar)) (layer (RD.coreBranch hG a).toNode : ℝ))
            (WaveTurbulence.VineEstS3.Eng.outSet (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer)
              (qOutOf RD hG layer a b R) centre wBar) Pe.L Pe.γ Pe.η) β') ∧
        ‖(coupling Pe.d Pe.L Pe.γ Pe.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ * q ≤
          ENNReal.ofReal ((1 + |lam|) ^ (6 * Pe.η ^ 6) * ((engNs Pe.η Pe.C₁ Km Kr * Real.sqrt Pe.δ) ^ clLocalOrder2 RD hG R *
            (Kb ^ (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card *
            Pe.L ^ (-(Pe.η ^ 8 * ((Famb.VineEstS3.cohmolIndexΓ B RD hG layer +
              (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
              Pe.η ^ 2 * ((Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7)) *
            regionLeafSize RD hG R layer hLayer (fun _ => B₀))) := by
  intro ψ hψ
  have hd1 : 1 ≤ Pe.d := hPe.hd1
  have hL0 : 0 < Pe.L := by linarith
  have hC1' : 1 ≤ Pe.C₁ := E.hC
  have hδ : 0 < Pe.δ := hPe.hδ
  have hη0 : 0 < Pe.η := hPe.hη0
  have hη1 : Pe.η ≤ 1 := by have := hPe.hη1; linarith
  have hcb : 0 < rowCb Pe := by unfold rowCb; have := WaveTurbulence.PL2330.cLeib_nonneg Pe.d (30 * Pe.d); linarith
  set κ := kparOf Pe.L Pe.γ Pe.δ h wBar with hκ
  have Re : RemEnv Pe κ := ⟨hd1, by linarith, hδ, hPe.hθη, rfl, rfl⟩
  have hL : κ.L ≠ 0 := hL0.ne'
  set SFF := Famb.VineEstS5C.P4.W13.sffOfΓ (hprime := hprime) B RD hG layer hLayer E hord with hSFF
  set BSFF := Famb.VineEstS5C.P4.Final.botSffOfΓ B RD hG layer hLayer hprime E hord with hBSFF
  have hQ := Famb.VineEstS5C.P4.W2.hfreeAt_holds_famΓ B RD hG layer hLayer hR SFF hprime BSFF hM9 hL hcan ψ hψ
  obtain ⟨recs, Dm, ⟨hexc, hnp, hnb, hDm', hNE'⟩, hfree⟩ := hQ
  have hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U := fun r hr => (hexc r hr).2.1
  have hbjI : ∀ r ∈ recs, r.bj ∈ clInteriorBranches R := fun r hr => (hexc r hr).2.2
  have hblkinj : ∀ r ∈ recs, ∀ r' ∈ recs, r.blk = r'.blk → r = r' := by
    intro r hr r' hr' hb
    have hp := Famb.VineEstS5C.P4.W2.excOf_block_injΓ B RD hG layer hLayer _ _ _ _ (hexc r hr).1 (hexc r' hr').1 (hreg r hr) (hreg r' hr') hb
    exact List.inj_on_of_nodup_map hnp hr hr' hp
  have blkOf : ∀ r (hr : r ∈ recs), (Famb.VineEstS3.assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩).1.val = r.blk := fun r hr =>
    Famb.VineEstS5C.P4.W2.excOf_pairBij_fstΓ B RD hG layer hLayer _ _ _ _ hM9 (hexc r hr).1 (hreg r hr)
  have hbjl : ∀ r ∈ recs, ∀ i : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B).I, r.blk = i.val →
      r.bj = (Famb.VineEstS2.assemblyClockAtomEquivΓ hM9 B (.inl ⟨i, 0⟩)).1 := fun r hr i hi =>
    Famb.VineEstS5C.P4.W2.excOf_bj_lowerΓ B RD hG layer hLayer _ _ _ _ hM9 (hexc r hr).1 i hi
  have hnorR : ∀ r ∈ recs, ∀ i : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B).I, r.blk = i.val → (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false :=
    fun r hr i hi => Famb.VineEstS5C.P4.W2.excOf_nor_falseΓ B RD hG layer hLayer _ _ _ _ hM9 (hexc r hr).1 i hi
  set W0 := Famb.VineEstS5C.P4.W2.termWΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar lam with hW0
  set KZ : ℝ := 4 * TR Pe.η ^ 2 * trC (6 * Pe.η ^ 6) ^ 2 / rowCb Pe ^ 2 with hKZ
  set Lw : ℝ := Pe.L ^ (-(Pe.gamma1 - Real.sqrt Pe.η)) with hLw
  let ZB : ↥(clRegionalPairs hG U) → ↥(clInteriorBranches R) → ℝ := fun p0 c0 =>
    Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer Pe (fun _ => B₀) W0 (Sum.inl (Famb.VineEstS3.assemblyPairBijΓ hG B hM9 p0)) *
      Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer Pe (fun _ => B₀) W0 (Sum.inr (Famb.VineEstS3.assemblyBranchBijΓ hM9 B c0))
  let srcS : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      Famb.VineEstS5C.P4.W2.StepSrcΓ B RD hG layer hLayer SFF lv pstar hk hop :=
    fun lv pstar hk hop => Famb.VineEstS5C.P4.W2.stepSrcCΓ B RD hG layer hLayer hprime Re E hord hC1' hB₀ lv pstar hk hop
  let srcB : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      Famb.VineEstS5C.P4.W2.BotSrcΓ B RD hG layer hLayer BSFF lv pstar h0 hop hmax :=
    fun lv pstar h0 hop hmax => Famb.VineEstS5C.P4.W2.botSrcCΓ B RD hG layer hLayer hprime Re E hord hC1' hB₀ lv pstar h0 hop hmax
  have hgS : ∀ lv pstar hk hop, Famb.VineEstS5C.P4.W2.StepGoodΓ B RD hG layer hLayer SFF lv pstar hk hop (srcS lv pstar hk hop) :=
    fun lv pstar hk hop b' hb' => hb'
  have hgB : ∀ lv pstar h0 hop hmax, Famb.VineEstS5C.P4.W2.BotGoodΓ B RD hG layer hLayer BSFF lv pstar h0 hop hmax (srcB lv pstar h0 hop hmax) :=
    fun lv pstar h0 hop hmax b' hb' => hb'
  have hszS : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (c' : (Famb.VineEstS5C.P4.bundleExpOfΓ B RD hG layer hLayer hR lv pstar hk (Famb.VineEstS5C.P4.zpSurj_of_opΓ B RD hG layer hLayer lv pstar hk hop)
        (Famb.VineEstS5C.P4.zpLayers_of_opΓ B RD hG layer hLayer lv pstar hk hop) (retParent _) (SFF lv pstar hk hop)).Ch)
      (p0 : ↥(clRegionalPairs hG U)) (_ : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
      (c0 : ↥(clInteriorBranches R)) (_ : c0.1 = (lv.split B RD hG layer hLayer pstar hk).sb.b),
      (srcS lv pstar hk hop).sz c' ≤ KZ * ZB p0 c0 * (if recKind c' = 3 then Lw else 1) := by
    intro lv pstar hk hop c' p0 hp0 c0 hc0
    refine Famb.VineEstS5C.P4.W2.stepSrcC_sz_rowsΓ B RD hG layer hLayer hM9 W0 hprime Re E hord hC1' hB₀ hη0 hη1 hcb hw lv pstar hk hop c' ?_ p0 hp0 c0 hc0
    intro b' hb'
    rcases hb' with hb' | hb' | hb' | hb' <;>
      first | exact Or.inl hb' | exact Or.inr hb' | (split_ifs at hb' <;> first | exact Or.inl hb' | exact Or.inr hb')
  have hszB : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
      (c : (Famb.VineEstS5C.P4.Bot.bundleBotFamOfΓ B RD hG layer hLayer hprime hR BSFF lv pstar h0 hop hmax).Ch)
      (p0 : ↥(clRegionalPairs hG U)) (_ : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
      (c0 : ↥(clInteriorBranches R)) (_ : c0.1 = lv.c.b),
      (srcB lv pstar h0 hop hmax).sz c ≤ KZ * ZB p0 c0 * (if recKind c = 3 then Lw else 1) := by
    intro lv pstar h0 hop hmax c p0 hp0 c0 hc0
    refine Famb.VineEstS5C.P4.W2.botSrcC_sz_rowsΓ B RD hG layer hLayer hM9 W0 hprime Re E hord hC1' hB₀ hη0 hη1 hcb hw lv pstar h0 hop hmax c ?_ p0 hp0 c0 hc0
    intro b' hb'
    rcases hb' with hb' | hb' | hb' | hb' <;>
      first | exact Or.inl hb' | exact Or.inr hb' | (split_ifs at hb' <;> first | exact Or.inl hb' | exact Or.inr hb')
  have hη4 : Pe.η < 1 / 4 := hPe.hη4
  have hKX1 : 1 ≤ K2.KxX Pe.η := (K2.KxX_spec hη0 hη4).1
  let xsS : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) →
        K2.XCross Pe (srcS lv pstar hk hop) :=
    fun lv pstar hk hop h => Famb.VineEstS5C.P4.W2.stepXCΓ B RD hG layer hLayer hprime Re E hord hC1' hB₀ hη0 hη4 lv pstar hk hop h
  let xsB : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) →
        K2.XCross Pe (srcB lv pstar h0 hop hmax) :=
    fun lv pstar h0 hop hmax h => Famb.VineEstS5C.P4.W2.botXCΓ B RD hG layer hLayer hprime Re E hord hC1' hB₀ hη0 hη4 lv pstar h0 hop hmax h
  have hRbq : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ (Pe.D : ℝ) := by
    intro lv pstar hop
    have h1 := zpQh_le_p (lv.state B RD hG layer hLayer) hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    have h2 := zpQ2_le_zpQ4 (lv.state B RD hG layer hLayer) hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    have h3 := zpQ4_le_zpQh (lv.state B RD hG layer hLayer) hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    have h4 : p < Pe.D := E.hp
    have h5 : zpQh (lv.state B RD hG layer hLayer) pstar + 1 ≤ Pe.D := by omega
    have h6 : zpQ2 (lv.state B RD hG layer hLayer) pstar + 1 ≤ Pe.D := by omega
    refine max_le ?_ ?_
    · exact_mod_cast h5
    · exact_mod_cast h6
  have hRbS : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ (Pe.D : ℝ) :=
    fun lv pstar _ hop => hRbq lv pstar hop
  have hRbB : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ (Pe.D : ℝ) :=
    fun lv pstar _ hop _ => hRbq lv pstar hop
  have hall : ∀ r (hr : r ∈ recs), ∃ (kd : ℕ) (zc : Prop) (addr : Finset ((Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar × (Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar)) (bnd : ℝ≥0∞),
      Famb.VineEstS5C.P4.W2.RecSpecΓ (P := Pe) (κ0 := κ) B RD hG layer hM9 hL r (hreg r hr) (hbjI r hr) kd zc addr bnd ∧
      bnd ≤ Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η)) * ENNReal.ofReal (KZ * ZB ⟨r.p0, hreg r hr⟩ ⟨r.bj, hbjI r hr⟩ * (if kd = 3 then Lw else 1)) :=
    fun r hr => Famb.VineEstS5C.P4.W2.exists_recSpecΓ B RD hG layer hLayer hR SFF hprime BSFF hdisp hd2 hM9 hL srcS hgS srcB hgB KZ Lw ZB hszS hszB xsS xsB (K2.KxX Pe.η) hKX1 (fun _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ _ => le_rfl) hRbS hRbB r
      (hexc r hr).1 (hreg r hr) (hbjI r hr)
  choose! kd zc addr bnd hsp using hall
  have hfreeR : ∀ i : Fin n, (∀ r ∈ recs, r.blk ≠ i.val) → (Famb.VineEstS2.assemblyPieceAtΓ B i).label.IsBad = true → ¬ Famb.VineEstS3.AClauseΓ hM9 B RD hG layer i →
      ∃ v : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx, v.1 = i ∧
        1 ≤ max (Famb.VineEstS3.rowCoupleGΓ hM9 B RD hG layer hLayer v) (Famb.VineEstS3.rowTreeGΓ hM9 B RD hG layer hLayer v) := by
    intro i hi hbad hnac
    rcases hfree i hbad hnac with ⟨r, hr, hh, hh2⟩ | hv
    · exact absurd ((blkOf r hr).symm.trans (by rw [hh2])) (hi r hr)
    · exact hv
  set Bx : Set (Fin 3 → ℝ) := openTop (WaveTurbulence.VineEstS3.Eng.outBox (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer)
    (qOutOf RD hG layer a b R) centre wBar)) (layer (RD.coreBranch hG a).toNode : ℝ) with hBxdef
  have hBx : Bx ⊆ WaveTurbulence.VineEstS3Par.Eng.outBox
      (Famb.VineEstS5C.P4.W2.natEngΓ hM9 B RD hG layer hLayer (qOutOf RD hG layer a b R) centre wBar lam) := openTop_subset _ _
  have hext : ∀ tt ∈ Bx, ((layC RD hG layer a : ℕ) : ℝ) < tt 0 ∧ tt 0 < (layC RD hG layer a : ℕ) + 1 := by
    intro tt htt
    obtain ⟨hbx, hne⟩ := htt
    have h0 := (hbx.1 0)
    have hne' : tt 0 ≠ ((layer (RD.coreBranch hG a).toNode : ℕ) : ℝ) ∧ tt 0 ≠ ((layer (RD.coreBranch hG a).toNode : ℕ) : ℝ) + 1 := by
      constructor
      · intro he; exact hne (Or.inl he)
      · intro he; exact hne (Or.inr he)
    exact ⟨lt_of_le_of_ne h0.1 (Ne.symm hne'.1), lt_of_le_of_ne h0.2 hne'.2⟩
  obtain ⟨vpf, vbf, hvpf, hvbf⟩ := Famb.VineEstS5C.P4.W2.exists_row_mapsΓ hM9 B hG recs hreg hbjI
  have hspec : ∀ r (hr : r ∈ recs), Famb.VineEstS5C.P4.W2.RecSpecΓ (P := Pe) (κ0 := κ) B RD hG layer hM9 hL r (hreg r hr) (hbjI r hr)
      (kd r) (zc r) (addr r) (bnd r) := fun r hr => (hsp r hr).1
  have hNE : RowFormNE RD hG Pe.L Pe.γ Pe.δ h layer hLayer R wBar ψ Dm (pexOf recs) (bexOf recs) (xqOf recs) := by
    have := hNE'
    rw [Famb.VineEstS5C.P4.W2.top_region_eqΓ B] at this
    exact this
  have hDm : ∀ t u, u a = t 0 → (Dm t u ↔ DomX R (fun v => layer (RD.coreBranch hG v).toNode) (bexOf recs) (t 0) (t 1) (t 2) u) := by
    intro t u hu
    have := hDm' t u hu
    rw [Famb.VineEstS5C.P4.W2.top_region_eqΓ B] at this
    exact this
  obtain ⟨q, hqc, Rb, hqRb, hRbN, hRb1⟩ := hbody Pe rfl rfl hPe (le_refl _) E.hg hinc hC1' (by linarith) hw hηγ E.hp hsel E.hB
    (fun r _ => hB₀) hM9 B RD hG layer hLayer hlay hord hl1 centre wBar lam hcoh ψ Dm recs hNE hDm hnp hnb hreg hbjI hblkinj blkOf hbjl hnorR
    kd zc addr bnd hspec hfreeR Bx _ hBx hext rfl
  refine ⟨q, fun β' hβ' => Famb.VineEstS5C.P4.W2.termCertW_of_GΓ B hG κ (modPsi b lam ψ) _ _ β' (hqc β' hβ'), ?_⟩
  have hM1 : 1 ≤ clLocalOrder1 R := Famb.VineEstS3.M_posΓ hM9 B
  have hζ := norm_clLocalZeta R
  have hn2 := (Famb.VineEstS3.order2_eq'Γ hM9 B RD hG).symm
  set bb := (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card with hbbdef
  have hbb : recs.toFinset.card ≤ bb := by
    refine Finset.card_le_card_of_injOn (fun r => (vpf r).1) ?_ ?_
    · intro r hr
      have hr' := List.mem_toFinset.1 hr
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hnorR r hr' _ (by rw [hvpf r hr']; exact (blkOf r hr').symm)
    · intro r hr r' hr' he
      have hr1 := List.mem_toFinset.1 hr
      have hr1' := List.mem_toFinset.1 hr'
      refine hblkinj r hr1 r' hr1' ?_
      have this : ((vpf r).1 : ℕ) = (vpf r').1 := congrArg Fin.val he
      rw [hvpf r hr1, hvpf r' hr1'] at this
      rw [← blkOf r hr1, ← blkOf r' hr1']
      exact this
  have hKZ0 : 0 ≤ KZ := by positivity
  have hLw0 : 0 ≤ Lw := Real.rpow_nonneg hL0.le _
  have hrb0 : ∀ ρ, 0 ≤ Famb.VineEstS5C.rowBoundHΓ hM9 B RD hG layer hLayer Pe (fun _ => B₀) W0 ρ :=
    fun ρ => Famb.VineEstS5C.P4.W2.rowBoundH_nonnegΓ E.hB hM9 B RD hG layer hLayer hlay hC1' hδ hL0 W0 ρ
  have hvp : ∀ r ∈ recs, (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG (vpf r)).1 = r.p0 := fun r hr => by
    rw [hvpf r hr, Famb.VineEstS4.assemblyPairOf_bijΓ]
  have hinj1 : ∀ r ∈ recs, ∀ r' ∈ recs, vpf r = vpf r' → r = r' := by
    intro r hr r' hr' he
    refine hblkinj r hr r' hr' ?_
    rw [← blkOf r hr, ← blkOf r' hr', ← hvpf r hr, ← hvpf r' hr', he]
  have hinj2 : ∀ r ∈ recs, ∀ r' ∈ recs, vbf r = vbf r' → r = r' := by
    intro r hr r' hr' he
    rw [hvbf r hr, hvbf r' hr'] at he
    have := congrArg (fun z : ↥(clInteriorBranches R) => z.1) ((Famb.VineEstS3.assemblyBranchBijΓ hM9 B).injective he)
    exact List.inj_on_of_nodup_map hnb hr hr' this
  have hcfnn : 0 ≤ cf := (ENNReal.toReal_nonneg).trans hcf
  have hX0 : 0 ≤ cf * 2 * (rowCb Pe * Pe.C₁ ^ 2) := by positivity
  have hrows := Famb.VineEstS5C.P4.W2.hrows_recΓ (P := Pe) E.hB hM9 B RD hG layer hLayer hlay recs kd zc addr centre wBar lam (by linarith) hC1' hδ hw hCt cf hcf vpf vbf hvp
    hinj1 hinj2 bnd Rb
    (fun ρ hρ => hRbN ρ (fun r hr => by
      have := hρ r hr
      rwa [hvpf r hr, hvbf r hr] at this))
    (fun r hr => by rw [hvpf r hr]; exact (hRb1 r hr).1)
    (fun r hr => by rw [hvbf r hr]; exact (hRb1 r hr).2)
    ((Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η))).toReal * KZ) (by positivity)
    (fun r hr => by
      have hbn := (hsp r hr).2
      have key := rec_bnd_le (K := Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η))) (Kall_ne_top Pe.d (ENNReal.mul_ne_top hK0t ENNReal.ofReal_ne_top)) (KZ := KZ) hKZ0
        (hrb0 (Sum.inl (Famb.VineEstS3.assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩))) (hrb0 (Sum.inr (Famb.VineEstS3.assemblyBranchBijΓ hM9 B ⟨r.bj, hbjI r hr⟩)))
        hLw0 hC1 (kd r = 3)
      rw [hvpf r hr, hvbf r hr]
      exact hbn.trans key)
    Kr Kb hKr hKb hKb1 hX0 hbb
  have hnum : Famb.VineEstS3.cohmolIndexΓ B RD hG layer + (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ ≤
      (Famb.VineEstS5C.P4.W2.recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).M₀ + (Famb.VineEstS5C.P4.W2.recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).M₁ := by
    have h0 := Famb.VineEstS3.cohmolIndex_le_M0Γ hM9 B RD hG layer
      (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) rfl
    have h1 := Famb.VineEstS5C.P4.W2.recM1_geΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam
    exact Nat.add_le_add h0 h1
  have hmass : tcSq Pe.η * ((3 : ℝ) ^ (clLocalOrder1 R + 1)) ≤ Km ^ (clLocalOrder1 R + 1) := by
    have hT0 : 0 ≤ tcSq Pe.η := ENNReal.toReal_nonneg
    have hm1 : (1 : ℝ) ≤ max (tcSq Pe.η) 1 := le_max_right _ _
    calc tcSq Pe.η * (3 : ℝ) ^ (clLocalOrder1 R + 1) ≤ max (tcSq Pe.η) 1 * (3 : ℝ) ^ (clLocalOrder1 R + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max (tcSq Pe.η) 1 ^ (clLocalOrder1 R + 1) * (3 : ℝ) ^ (clLocalOrder1 R + 1) :=
          mul_le_mul_of_nonneg_right (by
            calc max (tcSq Pe.η) 1 = max (tcSq Pe.η) 1 ^ 1 := (pow_one _).symm
              _ ≤ max (tcSq Pe.η) 1 ^ (clLocalOrder1 R + 1) := pow_le_pow_right₀ hm1 (by omega)) (by positivity)
      _ = (3 * max (tcSq Pe.η) 1) ^ (clLocalOrder1 R + 1) := by rw [← mul_pow]; ring
      _ ≤ Km ^ (clLocalOrder1 R + 1) := pow_le_pow_left₀ (by positivity) hKm _
  have hlf : 0 ≤ Kb ^ bb * regionLeafSize RD hG R layer hLayer (fun _ => B₀) :=
    mul_nonneg (pow_nonneg (by linarith) _) (Famb.VineEstS5C.regionLeafSize_nonnegΓ E.hB hM9 B RD hG layer hLayer hlay W0)
  have hlit := engine_literal (D := Famb.VineEstS5C.P4.W2.recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) q
    ((3 : ℝ) ^ (clLocalOrder1 R + 1)) Rb hqRb (clLocalZeta R) hζ (M := clLocalOrder1 R)
    (Sn := (∑ v : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx, (Famb.VineEstS3.rowCoupleΓ hM9 B RD hG v).size / 2) +
      ∑ v : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx, (Famb.VineEstS3.rowTreeΓ hM9 B RD v).size / 2)
    (n2 := clLocalOrder2 RD hG R) (bb := bb) (M0s := Famb.VineEstS3.cohmolIndexΓ B RD hG layer)
    (M1s := (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁)
    (Λ := (1 + |lam|) ^ (6 * Pe.η ^ 6)) (Km := Km) (Kr := Kr)
    (lf := Kb ^ bb * regionLeafSize RD hG R layer hLayer (fun _ => B₀))
    (Famb.VineEstS2.assemblyShape_MΓ hM9 B) hM1 hn2 rfl hnum (by positivity) hmass hKm1
    (Famb.VineEstS5C.P4.W2.maxPar_rec_leΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam Pe.η hη0) hrows hKr1 hlf (by linarith) hδ hC1' hη0 hη1
  refine hlit.trans (le_of_eq ?_)
  congr 1
  ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open VineParamContract
open scoped ENNReal
open WaveTurbulence.VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.W2
open Set
variable {γF : ℝ}
variable {kind : Bool}
variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

/-- **`Famb.VineEstS5C.P4.Final.UniformTermCertAtKΓ` for all kinds** (the dispatches `DispK01`, `DispK2` at the clock radius `D` and one constant `K0`). -/
theorem uniformTermCertAt_recSΓ {Pe : WTParams} (hPe : AmbP 6561 Pe) (hL2 : 2 ≤ Pe.L) (hηγ : Pe.η ≤ Pe.γ)
    (hw : 0 ≤ Pe.gamma1 - Real.sqrt Pe.η)
    {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCt : C ≠ ⊤) (hbody : TermRecBodySΓ (γF := γF) (A := 6561) Pe.d Pe.η C)
    {K0 : ℝ≥0∞} (hK0t : K0 ≠ ⊤) (hdisp : DispK01.{0} Pe K0) (hd2 : DispK2.{0} Pe (Pe.D : ℝ) K0)
    (cf Kr Kb Km : ℝ) (hcf : C.toReal ≤ cf) (hKr : cf * 2 * (rowCb Pe * Pe.C₁ ^ 2) ≤ Kr) (hKr1 : 1 ≤ Kr)
    (hKb : (Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η))).toReal * (4 * TR Pe.η ^ 2 * trC (6 * Pe.η ^ 6) ^ 2 / rowCb Pe ^ 2) ≤ Kb) (hKb1 : 1 ≤ Kb)
    (hKm1 : 1 ≤ Km) (hKm : 3 * max (tcSq Pe.η) 1 ≤ Km) :
    UniformTermCertAtKSΓ (γF := γF) 6561 Pe Km Kr Kb := by
  unfold UniformTermCertAtKSΓ
  intro p h B₀ wBar hB₀ E hinc hsel w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre lam hR hcoh
  have hall := term_rec_existsSΓ hPe hL2 hηγ hw hC1 hCt hbody hK0t hdisp hd2 cf Kr Kb Km hcf hKr hKr1 hKb hKb1 hKm1 hKm h B₀ wBar hB₀ E hinc hsel
    hprime hM9 B RD hG layer hLayer hcan hlay hord hl1 centre lam hR hcoh
  have hL0 : 0 < Pe.L := by linarith
  have hδ : 0 < Pe.δ := hPe.hδ
  have hc : ((coupling Pe.d Pe.L Pe.γ Pe.δ : ℝ) : ℂ) ≠ 0 := by
    have : 0 < coupling Pe.d Pe.L Pe.γ Pe.δ := by unfold coupling; positivity
    exact_mod_cast this.ne'
  have hζ0 : clLocalZeta R ≠ 0 := by
    intro h0
    have := norm_clLocalZeta R
    rw [h0, norm_zero] at this
    norm_num at this
  set N : ℝ≥0∞ := ‖(coupling Pe.d Pe.L Pe.γ Pe.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ with hN
  have hN0 : N ≠ 0 := (enorm_ne_zero).2 (mul_ne_zero (pow_ne_zero _ hc) hζ0)
  have hNt : N ≠ ⊤ := enorm_ne_top
  set lit : ℝ≥0∞ := ENNReal.ofReal ((1 + |lam|) ^ (6 * Pe.η ^ 6) * ((engNs Pe.η Pe.C₁ Km Kr * Real.sqrt Pe.δ) ^ clLocalOrder2 RD hG R *
            (Kb ^ (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card *
            Pe.L ^ (-(Pe.η ^ 8 * ((Famb.VineEstS3.cohmolIndexΓ B RD hG layer +
              (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
              Pe.η ^ 2 * ((Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7)) *
            regionLeafSize RD hG R layer hLayer (fun _ => B₀))) with hlit
  refine ⟨lit / N, fun ψ hψ => ?_, ?_⟩
  · obtain ⟨q, hq, hbound⟩ := hall ψ hψ
    refine hq (lit / N) ?_
    refine (ENNReal.le_div_iff_mul_le (Or.inl hN0) (Or.inl hNt)).2 ?_
    rw [mul_comm]; exact hbound
  · exact ENNReal.mul_div_le

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open VineParamContract
open scoped ENNReal
open WaveTurbulence.VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.W2
open Set
variable {γF : ℝ}
variable {kind : Bool}

/-- **`UniformTermCertTargetKSΓ`**: main's `Famb.VineEstS5C.P4.Final.UniformTermCertTargetKΓ` with every selector bound after the record. -/
def UniformTermCertTargetKSΓ : Prop :=
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
    ∀ {u : Unit} [_I : VineEst.RowSel u], UniformTermCertAtKSΓ (γF := γF) 6561 (⟨d, γ, η, φin, τstar, φ, c0, ν, δ, D, C₂, L⟩ : WTParams) Km Kr Kb

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open VineParamContract
open scoped ENNReal
open WaveTurbulence.VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.W2
open Set
variable {γF : ℝ}
variable {kind : Bool}

/-- **`Famb.VineEstS5C.P4.Final.UniformTermCertTargetKΓ`** (TARGET `Famb.VineEstS5C.P4.Final.UniformTermCertAtKΓ`, every kind). -/
theorem uniformTermCertKSΓ : UniformTermCertTargetKSΓ (γF := γF) := by
  intro d hd γ hγ
  have hd1 : 1 ≤ d := by omega
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hg1pos : 0 < g1 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : 0 < 2 * γ := by linarith [hγ.1]
    have h2 : 0 < 2 * ((d : ℝ) - 1) * (1 - γ) := by
      have : 0 < 1 - γ := by linarith [hγ.2]
      have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
      positivity
    exact lt_min h1 (lt_min one_pos h2)
  refine ⟨min γ (g1 ^ 2), lt_min hγ.1 (by positivity), fun η hη φin hφin τstar hτ φ hsol c0 hc0 => ?_⟩
  have hηγ : η ≤ γ := hη.2.trans (min_le_left _ _)
  have hηg : η ≤ g1 ^ 2 := hη.2.trans (min_le_right _ _)
  have hsq : Real.sqrt η ≤ g1 := by
    calc Real.sqrt η ≤ Real.sqrt (g1 ^ 2) := Real.sqrt_le_sqrt hηg
      _ = g1 := Real.sqrt_sq hg1pos.le
  obtain ⟨C, hC1, hCt, hbody⟩ := termCertWG_recSΓ (A := 6561) d η hd1
  let P₀ : WTParams := ⟨d, γ, η, φin, τstar, φ, c0, 0, 1, 0, 0, 2⟩
  obtain ⟨K00, hK00t, hK001, hdisp0⟩ := dispK01_uniform.{0} (A := 6561) P₀
  set cf : ℝ := max C.toReal 1 with hcf
  set Kr : ℝ := max 1 (cf * 2 * (rowCb P₀ * c0 ^ 2)) with hKr
  refine ⟨3 * max (tcSq η) 1, Kr, ?_, le_max_left _ _, fun ν δ D hδ hτD => ?_⟩
  swap
  · obtain ⟨K02, hK02t, hK021, hdisp2⟩ := dispK2_uniform.{0} (A := 6561) P₀ (D : ℝ)
    set K0 : ℝ≥0∞ := K00 ⊔ K02 with hK0def
    have hK0t : K0 ≠ ⊤ := (max_lt (lt_top_iff_ne_top.2 hK00t) (lt_top_iff_ne_top.2 hK02t)).ne
    set Kb : ℝ := max 1 ((Kall d (K0 * ENNReal.ofReal (K2.KxX η))).toReal * (4 * TR η ^ 2 * trC (6 * η ^ 6) ^ 2 / rowCb P₀ ^ 2)) with hKb
    refine ⟨Kb, le_max_left _ _, fun C₂ L hL hamb u _I => ?_⟩
    have hPe : WaveTurbulence.VineEstS5C.P2.AmbP 6561 (⟨d, γ, η, φin, τstar, φ, c0, ν, δ, D, C₂, L⟩ : WTParams) := hamb
    exact @uniformTermCertAt_recSΓ _ _ _I (⟨d, γ, η, φin, τstar, φ, c0, ν, δ, D, C₂, L⟩ : WTParams) hPe hL hηγ
      (by show 0 ≤ g1 - Real.sqrt η; linarith) C hC1 hCt hbody K0 hK0t
      (DispK01.mono (hdisp0 ν δ D C₂ L hamb) le_sup_left) (DispK2.mono (hdisp2 ν δ D C₂ L hamb) le_sup_right)
      cf Kr Kb (3 * max (tcSq η) 1)
      (le_max_left _ _) (le_max_right _ _) (le_max_left _ _) (le_max_right _ _) (le_max_left _ _)
      (by have : (1 : ℝ) ≤ max (tcSq η) 1 := le_max_right _ _
          linarith)
      le_rfl
  · have : (1 : ℝ) ≤ max (tcSq η) 1 := le_max_right _ _
    linarith

end

end WaveTurbulence.GammaLow.Flower
