/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Facts
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Final
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Facts
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Final` (sha256 6515af80ccaa2060…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Step 3: the engine bound in the literal form `(C√δ)^{n₍₂₎} L^{-η⁸n₍₃₎ - η²b + η⁷}` -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.PL2330 VineParamContract TTree Reg Reg.Skeleton RegRed WaveTurbulence.GammaLow.Famb.VineEstS2
open scoped ENNReal
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section Parts
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (P : WTParams)
  (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d)

/-- The product of the row bounds. -/
theorem prod_rowBound_eqΓ (hL : 0 < P.L) (hg : W.g = rowCoupleGΓ hM9 B RD hG layer hLayer)
    (hg' : W.g' = rowTreeGΓ hM9 B RD hG layer hLayer) (cf : ℝ) :
    ∏ ρ : Row (sourceSumintDatumΓ hM9 B hG W), (cf * (2 * rowBoundΓ hM9 B RD hG layer hLayer P W ρ)) =
      (cf * 2 * (rowCb P * P.C₁ ^ 2)) ^ (2 * clLocalOrder1 R) *
        (2 * P.C₁ ^ 2 * P.δ) ^ ((∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowCoupleΓ hM9 B RD hG v).size / 2) +
          ∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowTreeΓ hM9 B RD v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((sourceSumintDatumΓ hM9 B hG W).M₁ : ℝ)) := by
  unfold Row
  rw [Fintype.prod_sum_type]
  have hc := prod_side cf (rowCb P * P.C₁ ^ 2) (2 * P.C₁ ^ 2 * P.δ) P.L (-(P.gamma1 - Real.sqrt P.η)) hL
    (fun v : (assemblyShapeΓ hM9 B).VIdx => (rowCoupleΓ hM9 B RD hG v).size / 2)
    (rowCoupleGΓ hM9 B RD hG layer hLayer)
  have ht := prod_side cf (rowCb P * P.C₁ ^ 2) (2 * P.C₁ ^ 2 * P.δ) P.L (-(P.gamma1 - Real.sqrt P.η)) hL
    (fun v : (assemblyShapeΓ hM9 B).VIdx => (rowTreeΓ hM9 B RD v).size / 2)
    (rowTreeGΓ hM9 B RD hG layer hLayer)
  have e1 : ∀ v, cf * (2 * rowBoundΓ hM9 B RD hG layer hLayer P W (Sum.inl v)) =
      cf * (2 * ((rowCb P * P.C₁ ^ 2) * (2 * P.C₁ ^ 2 * P.δ) ^ ((rowCoupleΓ hM9 B RD hG v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (rowCoupleGΓ hM9 B RD hG layer hLayer v : ℝ)))) := fun v => rfl
  have e2 : ∀ v, cf * (2 * rowBoundΓ hM9 B RD hG layer hLayer P W (Sum.inr v)) =
      cf * (2 * ((rowCb P * P.C₁ ^ 2) * (2 * P.C₁ ^ 2 * P.δ) ^ ((rowTreeΓ hM9 B RD v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (rowTreeGΓ hM9 B RD hG layer hLayer v : ℝ)))) := fun v => rfl
  simp_rw [e1, e2]
  beta_reduce at hc ht
  refine (congrArg₂ (· * ·) hc ht).trans ?_
  have hcard : Fintype.card (assemblyShapeΓ hM9 B).VIdx = clLocalOrder1 R := by
    rw [Sumint.card_vector_index, assemblyShape_MΓ]
  rw [hcard, show 2 * clLocalOrder1 R = clLocalOrder1 R + clLocalOrder1 R by ring]
  have hM1 : ((sourceSumintDatumΓ hM9 B hG W).M₁ : ℝ) =
      ((∑ v : (assemblyShapeΓ hM9 B).VIdx, rowCoupleGΓ hM9 B RD hG layer hLayer v : ℕ) : ℝ) +
        ((∑ v : (assemblyShapeΓ hM9 B).VIdx, rowTreeGΓ hM9 B RD hG layer hLayer v : ℕ) : ℝ) := by
    unfold SumintDatum.M₁
    rw [← Nat.cast_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    show W.g v + W.g' v = _
    rw [hg, hg']
  rw [hM1, mul_add, Real.rpow_add hL]
  simp only [pow_add]
  ring

end Parts

theorem order2_eq'Γ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain) :
    clLocalOrder2 RD hG R = clLocalOrder1 R + 2 * ((∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowCoupleΓ hM9 B RD hG v).size / 2) +
      ∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowTreeΓ hM9 B RD v).size / 2) := by
  rw [order2_eqΓ hM9 B RD hG, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 2
  · refine Finset.sum_congr rfl fun v _ => ?_
    exact (Nat.two_mul_div_two_of_even (code_size_even _)).symm
  · refine Finset.sum_congr rfl fun v _ => ?_
    exact (Nat.two_mul_div_two_of_even (chain_size_even _)).symm

end WaveTurbulence.GammaLow.Famb.VineEstS3
