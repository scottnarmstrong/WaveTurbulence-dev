/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Facts

/-! # Step 3: the engine bound in the literal form `(C√δ)^{n₍₂₎} L^{-η⁸n₍₃₎ - η²b + η⁷}` -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.PL2330 VineParamContract TTree Reg Reg.Skeleton RegRed
open scoped ENNReal
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem ccη_lt_top (η : ℝ) : ccη η < ⊤ := by
  unfold ccη
  exact Fourier.cutoffMultiplierConstant_lt_top _ (FS.cutQ_hasCompactSupport _) (FS.cutQ_contDiff _)

theorem one_le_ccη_toReal (η : ℝ) : 1 ≤ (ccη η + 1).toReal := by
  have h : ccη η + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨(ccη_lt_top η).ne, ENNReal.one_ne_top⟩
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top h).2 le_add_self

theorem prod_side {ι : Type*} [Fintype ι] (cf k q L e : ℝ) (hL : 0 < L) (n g : ι → ℕ) :
    ∏ i, (cf * (2 * (k * q ^ (n i) * L ^ (e * (g i : ℝ))))) =
      (cf * 2 * k) ^ Fintype.card ι * q ^ (∑ i, n i) * L ^ (e * ((∑ i, g i : ℕ) : ℝ)) := by
  have h1 : ∀ i, cf * (2 * (k * q ^ (n i) * L ^ (e * (g i : ℝ)))) = (cf * 2 * k) * q ^ (n i) * L ^ (e * (g i : ℝ)) :=
    fun i => by ring
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Finset.prod_pow_eq_pow_sum, ← Real.rpow_sum_of_pos hL, ← Finset.mul_sum]
  congr 3
  push_cast; rfl

section Parts
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (P : WTParams)
  (W : SumintWeightClockData (assemblyShape hM9 B) P.d)

/-- The product of the row bounds. -/
theorem prod_rowBound_eq (hL : 0 < P.L) (hg : W.g = rowCoupleG hM9 B RD hG layer hLayer)
    (hg' : W.g' = rowTreeG hM9 B RD hG layer hLayer) (cf : ℝ) :
    ∏ ρ : Row (sourceSumintDatum hM9 B hG W), (cf * (2 * rowBound hM9 B RD hG layer hLayer P W ρ)) =
      (cf * 2 * (rowCb P * P.C₁ ^ 2)) ^ (2 * clLocalOrder1 R) *
        (2 * P.C₁ ^ 2 * P.δ) ^ ((∑ v : (assemblyShape hM9 B).VIdx, (rowCouple hM9 B RD hG v).size / 2) +
          ∑ v : (assemblyShape hM9 B).VIdx, (rowTree hM9 B RD v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((sourceSumintDatum hM9 B hG W).M₁ : ℝ)) := by
  unfold Row
  rw [Fintype.prod_sum_type]
  have hc := prod_side cf (rowCb P * P.C₁ ^ 2) (2 * P.C₁ ^ 2 * P.δ) P.L (-(P.gamma1 - Real.sqrt P.η)) hL
    (fun v : (assemblyShape hM9 B).VIdx => (rowCouple hM9 B RD hG v).size / 2)
    (rowCoupleG hM9 B RD hG layer hLayer)
  have ht := prod_side cf (rowCb P * P.C₁ ^ 2) (2 * P.C₁ ^ 2 * P.δ) P.L (-(P.gamma1 - Real.sqrt P.η)) hL
    (fun v : (assemblyShape hM9 B).VIdx => (rowTree hM9 B RD v).size / 2)
    (rowTreeG hM9 B RD hG layer hLayer)
  have e1 : ∀ v, cf * (2 * rowBound hM9 B RD hG layer hLayer P W (Sum.inl v)) =
      cf * (2 * ((rowCb P * P.C₁ ^ 2) * (2 * P.C₁ ^ 2 * P.δ) ^ ((rowCouple hM9 B RD hG v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (rowCoupleG hM9 B RD hG layer hLayer v : ℝ)))) := fun v => rfl
  have e2 : ∀ v, cf * (2 * rowBound hM9 B RD hG layer hLayer P W (Sum.inr v)) =
      cf * (2 * ((rowCb P * P.C₁ ^ 2) * (2 * P.C₁ ^ 2 * P.δ) ^ ((rowTree hM9 B RD v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (rowTreeG hM9 B RD hG layer hLayer v : ℝ)))) := fun v => rfl
  simp_rw [e1, e2]
  beta_reduce at hc ht
  refine (congrArg₂ (· * ·) hc ht).trans ?_
  have hcard : Fintype.card (assemblyShape hM9 B).VIdx = clLocalOrder1 R := by
    rw [Sumint.card_vector_index, assemblyShape_M]
  rw [hcard, show 2 * clLocalOrder1 R = clLocalOrder1 R + clLocalOrder1 R by ring]
  have hM1 : ((sourceSumintDatum hM9 B hG W).M₁ : ℝ) =
      ((∑ v : (assemblyShape hM9 B).VIdx, rowCoupleG hM9 B RD hG layer hLayer v : ℕ) : ℝ) +
        ((∑ v : (assemblyShape hM9 B).VIdx, rowTreeG hM9 B RD hG layer hLayer v : ℕ) : ℝ) := by
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

theorem order2_eq' (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain) :
    clLocalOrder2 RD hG R = clLocalOrder1 R + 2 * ((∑ v : (assemblyShape hM9 B).VIdx, (rowCouple hM9 B RD hG v).size / 2) +
      ∑ v : (assemblyShape hM9 B).VIdx, (rowTree hM9 B RD v).size / 2) := by
  rw [order2_eq hM9 B RD hG, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 2
  · refine Finset.sum_congr rfl fun v _ => ?_
    exact (Nat.two_mul_div_two_of_even (code_size_even _)).symm
  · refine Finset.sum_congr rfl fun v _ => ?_
    exact (Nat.two_mul_div_two_of_even (chain_size_even _)).symm

end WaveTurbulence.VineEstS3
