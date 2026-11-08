/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.Sel
public import WaveTurbulence.Foundations.Flower.V5W.ContCore
public import WaveTurbulence.Foundations.Flower.V5W.ContMember
public import WaveTurbulence.Foundations.Flower.Stage1W.Inputs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRowH
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf
public import WaveTurbulence.Foundations.Spine.RA1LW.XNormBridge
public import WaveTurbulence.Foundations.Spine.RA1LW.NormScale
public import WaveTurbulence.Foundations.IncohInst.DecodingObligations

/-! # V5W-B-WORLD B3: the engine rows of selected incoherent rows

The selected rows of the W2 engine datum obey the same leaf-cost bound as main's native rows
(`VineEstS5C.coupleRow_leaf_le`/`treeRow_leaf_le`), for every selector:
* a coherent row (or a row of an unweighted selector) is main's `KQstar`/`KTstar` row;
* an incoherent row of a weighted selector is `cψ^{-(4n+2)}` (couples) / `cψ^{-(4n+1)}` (trees) times its top-weighted
  kernel, at its root parent layers, which are its clock-slot layers (`Flower.V5W.coupleRootParents_rowQ`); INC-TOP's
  normalized bound (`Stage1W.TopIncoherentDecayAt`) cancels the normalization exactly.
`SelOK P p` bundles what the weighted case reads: top layer `p`, the `GPresented (32 d)` presentation of the weight, and
INC-TOP's gate at `P`.  `natRows_resS`/`natRowHS` are main's `natRows_res`/`natRowH` (W2/NatRowH, plain-specialized on
main) for every selector, with the selector bound inside the constants.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine VineParamContract TTree Reg
  Reg.Skeleton RegRed WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W2 MeasureTheory
open scoped ENNReal

/-- Homogeneity (inequality form) of the restricted `X`-norm. -/
theorem XNormRestr_const_mul_le {r d : ℕ} {c : ℂ} (hc : c ≠ 0) (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ))
    (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ₁ Λ₂ B K (fun t k => c * F t k) ≤ ‖c‖ₑ * XNormRestr θ Λ₁ Λ₂ B K F := by
  have hc0 : ‖c‖ₑ ≠ 0 := by simpa using hc
  have hct : ‖c‖ₑ ≠ ⊤ := enorm_ne_top
  unfold XNormRestr
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf fun hG => ?_
  refine iInf_le_of_le (fun t k => c * G t k) (iInf_le_of_le (fun t ht k hk => by show c * G t k = c * F t k; rw [hG t ht k hk]) ?_)
  rw [RA1Leafwise.XNorm_eq_mixedFourierNorm, RA1Leafwise.XNorm_eq_mixedFourierNorm]
  exact (RA1Leafwise.mixedFourierNorm_smul hc θ Λ₁ Λ₂ G).le

section Sel
variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]

/-- **What a weighted selector reads at the top layer `p`**: its top layer is `p`, its weight is `GPresented (32 d)`
with constant `cψ`, and INC-TOP's gate holds at `P` (vacuous for an unweighted selector). -/
def SelOK (P : WTParams) (p : ℕ) : Prop :=
  rowSel.weighted = true →
    rowSel.p = p ∧ Stage1W.GPresented (32 * P.d) (rowSel.g P.d) rowSel.cψ ∧ Stage1W.TopIncoherentDecayAt P

theorem KQsel_weighted {d : ℕ} (hw : rowSel.weighted = true) {incoh : ℕ} (h : incoh ≠ 0) (q q' : ℕ) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (t s : ℝ) (k : Mom d) :
    VineEst.KQsel incoh q q' L γ δ F LG t s k =
      (((rowSel.cψ ^ (2 * LG.garden.order + 2))⁻¹ : ℝ) : ℂ) *
        Stage1W.coupleLeavesTop L γ δ rowSel.p (rowSel.g d) q q' LG (LGSpine.layerProfiles LG F) t s k := by
  unfold VineEst.KQsel
  rw [hw]
  simp only [cond_true, h, ↓reduceIte]

theorem KTsel_weighted {d : ℕ} (hw : rowSel.weighted = true) {incoh : ℕ} (h : incoh ≠ 0) (q : ℕ) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) (t s : ℝ) (k : Mom d) :
    VineEst.KTsel incoh q L γ δ F LG t s k =
      (((rowSel.cψ ^ (2 * LG.garden.order + 1))⁻¹ : ℝ) : ℂ) *
        Stage1W.treeLeavesTop L γ δ rowSel.p (rowSel.g d) q LG (LGSpine.layerProfiles LG F) t s k := by
  unfold VineEst.KTsel
  rw [hw]
  simp only [cond_true, h, ↓reduceIte]

/-- The normalization cancels the presentation constant of INC-TOP's bound. -/
theorem norm_cancel {c : ℝ} (hc : 1 ≤ c) (m : ℕ) (X : ℝ≥0∞) :
    ‖(((c ^ m)⁻¹ : ℝ) : ℂ)‖ₑ * (ENNReal.ofReal (c ^ m) * X) = X := by
  have hpos : 0 < c ^ m := pow_pos (by linarith) m
  have hn : ‖(((c ^ m)⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (c ^ m)⁻¹ := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hpos).le]
  rw [← mul_assoc, hn, ← ENNReal.ofReal_mul (inv_pos.2 hpos).le, inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable {hM9 : VINEPARAM} {B : CLChainAssembly G R n} {RD : ReconstructionData G} {hG : G.IsPlain}
  {layer : GNode (RD.forest hG) → ℕ} {hLayer : IsLayering (RD.garden hG) layer}
variable {P : WTParams} {p : ℕ}

/-- **Row bound, selected couples** (layer family, leaf cost). -/
theorem coupleRow_leaf_leS (W : SumintWeightClockData (assemblyShape hM9 B) P.d) {h : ℕ → Mom P.d → ℝ}
    {Bh : ℕ → ℝ} (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (hsel : SelOK P p)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx)
    (hel : CoupleEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d)
      (timeBox (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).1
        (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).2) Set.univ
      (fun ts k => VineEst.selCoupleRow P.L P.γ P.δ h RD hG layer hLayer (assemblyPairOf hM9 B hG v).1
        (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((rowCouple hM9 B RD hG v).size / 2) (rowCoupleG hM9 B RD hG layer hLayer v) *
        layerCost Bh (rowCoupleLG hM9 B RD hG layer hLayer v)) := by
  by_cases hc : rowSel.weighted = true ∧ rowCoupleG hM9 B RD hG layer hLayer v ≠ 0
  · obtain ⟨hwt, hg0⟩ := hc
    obtain ⟨hpp, hpres, htop⟩ := hsel hwt
    have hel' := hel
    obtain ⟨hqp, hq'p, hn, hr0, hr1, -⟩ := hel'
    have hwf : (rowCouple hM9 B RD hG v).wf = true := RD.couple_wf _
    have hsize : (rowCouple hM9 B RD hG v).size = 2 * ((rowCouple hM9 B RD hG v).size / 2) :=
      (Nat.two_mul_div_two_of_even (code_size_even _)).symm
    have hdec : (rowCouple hM9 B RD hG v).Decodes (rowCoupleLG hM9 B RD hG layer hLayer v).garden :=
      rowCouple_decodes v
    have hord : (rowCoupleLG hM9 B RD hG layer hLayer v).garden.order =
        2 * ((rowCouple hM9 B RD hG v).size / 2) :=
      (IncohInst.couple_size_eq_order _ hdec).trans hsize
    have hlay' : ∀ x, (rowCoupleLG hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _
    obtain ⟨e0, e1⟩ := Flower.V5W.coupleRootParents_rowQ hM9 B RD hG layer hLayer W hq hqo P.L P.γ P.δ h p v
    have hg0' : Flower.V5W.coupleIncoh RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 ≠ 0 := hg0
    have hexp : 2 * (rowCoupleLG hM9 B RD hG layer hLayer v).garden.order + 2 =
        4 * ((rowCouple hM9 B RD hG v).size / 2) + 2 := by rw [hord]; ring
    have hfun : (fun ts k => VineEst.selCoupleRow P.L P.γ P.δ h RD hG layer hLayer (assemblyPairOf hM9 B hG v).1
        (ts 0) (ts 1) k) = fun (ts : Fin 2 → ℝ) k =>
          (((rowSel.cψ ^ (4 * ((rowCouple hM9 B RD hG v).size / 2) + 2))⁻¹ : ℝ) : ℂ) *
          Stage1W.coupleLeavesTop P.L P.γ P.δ p (rowSel.g P.d)
            (Flower.V5W.coupleRootParents p RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 0)
            (Flower.V5W.coupleRootParents p RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 1)
            (rowCoupleLG hM9 B RD hG layer hLayer v)
            (LGSpine.layerProfiles (rowCoupleLG hM9 B RD hG layer hLayer v) h) (ts 0) (ts 1) k := by
      funext ts k
      unfold VineEst.selCoupleRow
      rw [KQsel_weighted hwt hg0', hpp]
      change (((rowSel.cψ ^ (2 * (rowCoupleLG hM9 B RD hG layer hLayer v).garden.order + 2))⁻¹ : ℝ) : ℂ) * _ = _
      rw [hexp]
      rfl
    have hbox : timeBox (Flower.V5W.coupleRootParents p RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 0)
        (Flower.V5W.coupleRootParents p RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 1) =
        timeBox (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).1
          (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inl v)).2 := by rw [e0, e1]
    rw [hfun]
    have hc1 := rowSel.one_le_cψ
    have hcne : (((rowSel.cψ ^ (4 * ((rowCouple hM9 B RD hG v).size / 2) + 2))⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < rowSel.cψ ^ (4 * ((rowCouple hM9 B RD hG v).size / 2) + 2) := pow_pos (by linarith) _
      exact_mod_cast (inv_pos.2 this).ne'
    refine (XNormRestr_mono_theta hη6 _ _ _ _ _).trans ?_
    refine (XNormRestr_const_mul_le hcne _ _ _ _ _ _).trans ?_
    have hg1 : 1 ≤ rowCoupleG hM9 B RD hG layer hLayer v := Nat.one_le_iff_ne_zero.mpr hg0
    have hT := (htop p hp _ hn (rowSel.g P.d) rowSel.cψ hc1 hpres).1 (rowCouple hM9 B RD hG v) hwf hsize
      (rowCoupleLG hM9 B RD hG layer hLayer v) hdec hlay'
      (Flower.V5W.coupleRootParents p RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 0)
      (Flower.V5W.coupleRootParents p RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 1) (by rw [e0]; exact hqp) (by rw [e1]; exact hq'p)
      (by rw [e0]; exact hr0) (by rw [e1]; exact hr1) hg1 _ _
      (Flower.V5W.controlled_layerProfiles_spine hB _ hlay')
    rw [leafSizeProduct_eq_layerCost hB _ hlay', hbox] at hT
    refine (mul_le_mul' le_rfl hT).trans ?_
    rw [mul_assoc, norm_cancel hc1]
    have hL0 : 0 ≤ P.L := by linarith
    rw [ENNReal.ofReal_mul (rowB_nonneg' (P := P) hC hδ (by linarith) _ _)]
    exact mul_le_mul' (regBound_le_rowB hC hδ hL0 _ _) le_rfl
  · have hfun : (fun ts k => VineEst.selCoupleRow P.L P.γ P.δ h RD hG layer hLayer (assemblyPairOf hM9 B hG v).1
        (ts 0) (ts 1) k) = fun (ts : Fin 2 → ℝ) k =>
          KQstar P.L P.γ P.δ h (rowCoupleLG hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k := by
      funext ts k
      unfold VineEst.selCoupleRow
      rcases not_and_or.mp hc with hw' | hg0
      · exact VineEst.KQsel_of_weighted_eq_false (by simpa using hw') _ _ _ _ _ _ _ _ _ _ _
      · exact VineEst.KQsel_of_incoh_eq_zero (not_not.mp hg0) _ _ _ _ _ _ _ _ _ _
    rw [hfun]
    exact coupleRow_leaf_le W hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hlay v hel

/-- **Row bound, selected trees** (layer family, leaf cost). -/
theorem treeRow_leaf_leS (W : SumintWeightClockData (assemblyShape hM9 B) P.d) {h : ℕ → Mom P.d → ℝ}
    {Bh : ℕ → ℝ} (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (hsel : SelOK P p)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hB : ProfileBound P h Bh p)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx)
    (hel : TreeEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) 0
      (timeBoxGt (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1
        (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2) Set.univ
      (fun ts k => VineEst.selTreeRow P.L P.γ P.δ h RD hG layer hLayer (assemblyBranchOf hM9 B v).1
        (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((rowTree hM9 B RD v).size / 2) (rowTreeG hM9 B RD hG layer hLayer v) *
        layerCost Bh (rowTreeLG hM9 B RD hG layer hLayer v)) := by
  by_cases hc : rowSel.weighted = true ∧ rowTreeG hM9 B RD hG layer hLayer v ≠ 0
  · obtain ⟨hwt, hg0⟩ := hc
    obtain ⟨hpp, hpres, htop⟩ := hsel hwt
    have hel' := hel
    obtain ⟨hqq, hqp, hn, hr0, hlone, -⟩ := hel'
    have hwf : (rowTree hM9 B RD v).wf = true := RD.tree_wf _
    have hsize : (rowTree hM9 B RD v).size = 2 * ((rowTree hM9 B RD v).size / 2) :=
      (Nat.two_mul_div_two_of_even (chain_size_even _)).symm
    have hdec : (rowTree hM9 B RD v).DecodesTree (rowTreeLG hM9 B RD hG layer hLayer v).garden := rowTree_decodes v
    have hord : (rowTreeLG hM9 B RD hG layer hLayer v).garden.order = 2 * ((rowTree hM9 B RD v).size / 2) :=
      (decodesTree_order' hdec).trans hsize
    have hlay' : ∀ x, (rowTreeLG hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _
    have e0 := Flower.V5W.treeRootParent_rowQ hM9 B RD hG layer hLayer W hq hqo P.L P.γ P.δ h p v
    have hg0' : Flower.V5W.treeIncoh RD hG layer hLayer (assemblyBranchOf hM9 B v).1 ≠ 0 := hg0
    have hexp : 2 * (rowTreeLG hM9 B RD hG layer hLayer v).garden.order + 1 =
        4 * ((rowTree hM9 B RD v).size / 2) + 1 := by rw [hord]; ring
    have hfun : (fun ts k => VineEst.selTreeRow P.L P.γ P.δ h RD hG layer hLayer (assemblyBranchOf hM9 B v).1
        (ts 0) (ts 1) k) = fun (ts : Fin 2 → ℝ) k =>
          (((rowSel.cψ ^ (4 * ((rowTree hM9 B RD v).size / 2) + 1))⁻¹ : ℝ) : ℂ) *
          Stage1W.treeLeavesTop P.L P.γ P.δ p (rowSel.g P.d)
            (Flower.V5W.treeRootParent p RD hG layer hLayer (assemblyBranchOf hM9 B v).1)
            (rowTreeLG hM9 B RD hG layer hLayer v)
            (LGSpine.layerProfiles (rowTreeLG hM9 B RD hG layer hLayer v) h) (ts 0) (ts 1) k := by
      funext ts k
      unfold VineEst.selTreeRow
      rw [KTsel_weighted hwt hg0', hpp]
      change (((rowSel.cψ ^ (2 * (rowTreeLG hM9 B RD hG layer hLayer v).garden.order + 1))⁻¹ : ℝ) : ℂ) * _ = _
      rw [hexp]
      rfl
    have hbox : timeBoxGt (Flower.V5W.treeRootParent p RD hG layer hLayer (assemblyBranchOf hM9 B v).1)
        (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 =
        timeBoxGt (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1
          (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 := by rw [e0]
    rw [hfun]
    have hc1 := rowSel.one_le_cψ
    have hcne : (((rowSel.cψ ^ (4 * ((rowTree hM9 B RD v).size / 2) + 1))⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < rowSel.cψ ^ (4 * ((rowTree hM9 B RD v).size / 2) + 1) := pow_pos (by linarith) _
      exact_mod_cast (inv_pos.2 this).ne'
    refine (XNormRestr_mono_theta hη6 _ _ _ _ _).trans ?_
    refine (XNormRestr_const_mul_le hcne _ _ _ _ _ _).trans ?_
    have hg1 : 1 ≤ rowTreeG hM9 B RD hG layer hLayer v := Nat.one_le_iff_ne_zero.mpr hg0
    have hT := (htop p hp _ hn (rowSel.g P.d) rowSel.cψ hc1 hpres).2 (rowTree hM9 B RD v) hwf hsize
      (rowTreeLG hM9 B RD hG layer hLayer v) hdec hlay'
      (Flower.V5W.treeRootParent p RD hG layer hLayer (assemblyBranchOf hM9 B v).1)
      (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 (by rw [e0]; exact hqq) (by rw [e0]; exact hqp)
      (by rw [e0]; exact hr0) hlone hg1 _ _
      (Flower.V5W.controlled_layerProfiles_spine hB _ hlay')
    rw [leafSizeProduct_eq_layerCost hB _ hlay', hbox] at hT
    refine (mul_le_mul' le_rfl hT).trans ?_
    rw [mul_assoc, norm_cancel hc1]
    have hL0 : 0 ≤ P.L := by linarith
    rw [ENNReal.ofReal_mul (rowB_nonneg' (P := P) hC hδ (by linarith) _ _)]
    exact mul_le_mul' (regBound_le_rowB hC hδ hL0 _ _) le_rfl
  · have hfun : (fun ts k => VineEst.selTreeRow P.L P.γ P.δ h RD hG layer hLayer (assemblyBranchOf hM9 B v).1
        (ts 0) (ts 1) k) = fun (ts : Fin 2 → ℝ) k =>
          KTstar P.L P.γ P.δ h (rowTreeLG hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k := by
      funext ts k
      unfold VineEst.selTreeRow
      rcases not_and_or.mp hc with hw' | hg0
      · exact VineEst.KTsel_of_weighted_eq_false (by simpa using hw') _ _ _ _ _ _ _ _ _ _
      · exact VineEst.KTsel_of_incoh_eq_zero (not_not.mp hg0) _ _ _ _ _ _ _ _ _
    rw [hfun]
    exact treeRow_leaf_le W hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hlay v hel

/-- **`hres` of the engine for selected rows** (main's `W2.natRows_res`, every selector). -/
theorem natRows_resS {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) {p : ℕ} (hp : p < P.D) (hsel : SelOK P p) {h : ℕ → Mom P.d → ℝ}
    {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (W : SumintWeightClockData (assemblyShape hM9 B) P.d)
    (hqW : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqoW : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
    (hel : ∀ v, CoupleEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
      TreeEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v)
    (ρ : VineEstS3.Eng.Row (sourceSumintDatum hM9 B hG W)) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (VineEstS3.Eng.rowOrder (sourceSumintDatum hM9 B hG W) ρ)
      (rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ) Set.univ
      ((assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ) <
      ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) := by
  have hL0 : 0 < P.L := by linarith
  rcases ρ with v | v
  · have h1 := coupleRow_leaf_leS W hgate hinc hsel hqW hqoW hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).1
    have hx : 0 < rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inl v) :=
      mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_pos hBpos hlay W _)
    refine h1.trans_lt ?_
    change ENNReal.ofReal (rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inl v)) < _
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  · have h1 := treeRow_leaf_leS W hgate hinc hsel hqW hqoW hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).2
    have hx : 0 < rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inr v) :=
      mul_pos (rowB_pos hC hδ hL0 _ _) (rowCostH_pos hBpos hlay W _)
    refine h1.trans_lt ?_
    change ENNReal.ofReal (rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inr v)) < _
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

end Sel

/-- **A selected row of the engine datum as a `RowData`, with the leaf-cost bound** (main's `W2.natRowH`, every
selector; the selector is bound after the constant). -/
theorem natRowHS (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {u : Unit} [_I : VineEst.RowSel u] (P : WTParams), P.d = d → P.η = η →
      ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ},
      ∀ {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
      (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
      (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L)
      (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (hp : p < P.D) (hsel : SelOK P p) (hB : ProfileBound P h Bh p)
      (hBpos : ∀ r ≤ p, 0 < Bh r)
      (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
      (W : SumintWeightClockData (assemblyShape hM9 B) P.d)
      (hqW : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
      (hqoW : W.qOut 0 = layer (RD.coreBranch hG a).toNode)
      (hel : ∀ v, CoupleEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
        TreeEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v)
      (hqq : ∀ v, (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
        (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1)
      (wN wDec : ℕ) (hwN : wN + 1 = 30 * P.d) (hwDec : wDec = 30 * P.d)
      (bk : Fin (assemblyShape hM9 B).I → Fin 4)
      (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
      (ρ : WaveTurbulence.VineEstS3Par.Eng.Row (engDatum hM9 B hG W wN wDec bk cons g g'))
      (slot : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot (engDatum hM9 B hG W wN wDec bk cons g g')),
      ∃ Rr : RowData (engDatum hM9 B hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ,
        (∀ cl : Fin 3 → ℝ, ![cl 0, cl 1] ∈ rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ → ∀ r k,
          Rr.W cl r k = (assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ ![cl 0, cl 1] k) ∧
        (∀ i, Rr.slot i = slot i) ∧
        Rr.b ≤ C * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) ∧
        Rr.Ae (assemblyShape_I_pos hM9 B) ∧ (∀ cl r k, Rr.W cl r k = ∑' m, Rr.c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl) := by
  obtain ⟨C, hC0, hCall⟩ := natRowData d η hd
  refine ⟨C, hC0, fun {u} _I P hPd hPη {w G U a b R n} {h Bh p} hgate hinc hη6 hη2 hC hδ hL hw hp hsel hB hBpos hM9 B RD hG
    layer hLayer hlay W hqW hqoW hel hqq wN wDec hwN hwDec bk cons g g' ρ slot => ?_⟩
  subst hPd hPη
  have hres := natRows_resS hgate hinc hd hη6 hη2 hC hδ hL hw hp hsel hB hBpos hM9 B RD hG layer hLayer hlay W hqW hqoW
    hel ρ
  have hord : VineEstS3.Eng.rowOrder (sourceSumintDatum hM9 B hG W) ρ =
      WaveTurbulence.VineEstS3Par.Eng.rowOrder (engDatum hM9 B hG W wN wDec bk cons g g') ρ := by
    rcases ρ with v | v
    · simp [VineEstS3.Eng.rowOrder, WaveTurbulence.VineEstS3Par.Eng.rowOrder, hwDec]
      rfl
    · rfl
  rw [hord] at hres
  exact hCall (engDatum hM9 B hG W wN wDec bk cons g g') (assemblyShape_I_pos hM9 B) hwN hwDec ρ slot _ _
    ((assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ) _ ENNReal.ofReal_ne_top
    (rowBx_subset_cell hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ)
    (rowBx_closure hM9 B RD hG layer hLayer W P.L P.γ P.δ h hqq ρ)
    (fun k => rows_continuousH hB hd hL hlay W ρ k) hres

end WaveTurbulence.Flower.V5WB
