/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCert
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNum1

/-! # P4-W2 (session 18, step 4c-2): native row bounds at a pair row and a branch row

`rowBoundH_inl_bij`, `rowBoundH_inr_bij`: `rowBoundH` at `assemblyPairBij p0` / `assemblyBranchBij c0` is `rowB (size/2) g · layerCost`.  `sz_le_rows`: the algebra
`4 TR² C₁⁴ (C₁² δ)^N (cost_C cost_T) ≤ (4 TR²/cb²) · rowB nC' 0 cost_C' · rowB nT' 0 cost_T'` for `nC' + nT' = N`, `cost_C cost_T = cost_C' cost_T'`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)



variable {Bh : ℕ → ℝ}

theorem rowBoundH_inl_bij (hM9 : VineParamContract.VINEPARAM) (W : SumintWeightClockData (assemblyShape hM9 B) P.d)
    (p0 : ↥(clRegionalPairs hG U)) :
    rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inl (assemblyPairBij hG B hM9 p0)) =
      rowB P ((RD.couple p0.1).size / 2) (rowCoupleG hM9 B RD hG layer hLayer (assemblyPairBij hG B hM9 p0)) *
        layerCost Bh (nativeCoupleLayered RD hG layer hLayer p0.1) := by
  simp only [rowBoundH, rowBound, rowCostH, rowCouple, rowCoupleLG, assemblyPairOf_bij hM9 B hG p0]

theorem rowBoundH_inr_bij (hM9 : VineParamContract.VINEPARAM) (W : SumintWeightClockData (assemblyShape hM9 B) P.d)
    (c0 : ↥(clInteriorBranches R)) :
    rowBoundH hM9 B RD hG layer hLayer P Bh W (Sum.inr (assemblyBranchBij hM9 B c0)) =
      rowB P ((RD.tree c0.1).size / 2) (rowTreeG hM9 B RD hG layer hLayer (assemblyBranchBij hM9 B c0)) *
        layerCost Bh (nativeChainLayered RD hG layer hLayer c0.1) := by
  simp only [rowBoundH, rowBound, rowCostH, rowTree, rowTreeLG, assemblyBranchOf_bij hM9 B c0]

theorem sz_le_rows (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hcb : 0 < rowCb P) {nC' nT' N : ℕ} (hs' : nC' + nT' = N)
    (cc tt cc' tt' T : ℝ) (hc : cc * tt = cc' * tt') (hcc' : 0 ≤ cc') (htt' : 0 ≤ tt') :
    4 * T ^ 2 * P.C₁ ^ 4 * (P.C₁ ^ 2 * P.δ) ^ N * (cc * tt) ≤
      (4 * T ^ 2 / rowCb P ^ 2) * (rowB P nC' 0 * cc' * (rowB P nT' 0 * tt')) := by
  have hC0 : 0 < P.C₁ := by linarith
  have e1 : rowB P nC' 0 * rowB P nT' 0 = rowCb P ^ 2 * P.C₁ ^ 4 * (2 * P.C₁ ^ 2 * P.δ) ^ N := by
    unfold rowB
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    rw [← hs', pow_add]
    ring
  have e2 : rowB P nC' 0 * cc' * (rowB P nT' 0 * tt') = (rowB P nC' 0 * rowB P nT' 0) * (cc' * tt') := by ring
  rw [e2, e1, hc]
  have h2N : (P.C₁ ^ 2 * P.δ) ^ N ≤ (2 * P.C₁ ^ 2 * P.δ) ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg P.C₁, mul_pos (pow_pos hC0 2) hδ]
  have hnn : 0 ≤ cc' * tt' := mul_nonneg hcc' htt'
  have hcb2 : rowCb P ^ 2 ≠ 0 := by positivity
  calc 4 * T ^ 2 * P.C₁ ^ 4 * (P.C₁ ^ 2 * P.δ) ^ N * (cc' * tt')
      ≤ 4 * T ^ 2 * P.C₁ ^ 4 * (2 * P.C₁ ^ 2 * P.δ) ^ N * (cc' * tt') := by
        apply mul_le_mul_of_nonneg_right _ hnn
        apply mul_le_mul_of_nonneg_left h2N (by positivity)
    _ = 4 * T ^ 2 / rowCb P ^ 2 * (rowCb P ^ 2 * P.C₁ ^ 4 * (2 * P.C₁ ^ 2 * P.δ) ^ N * (cc' * tt')) := by
        field_simp
