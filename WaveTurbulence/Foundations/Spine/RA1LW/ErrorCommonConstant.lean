/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.ErrorGeometricBudget

/-! # One order-independent constant for the explicit full physical error budget -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Incoh WaveTurbulence.Fourier
open scoped ENNReal

/-- Every factor in the checked full mixed-norm budget is absorbed by a
single geometric constant, chosen before the code, delta and order cutoff. -/
theorem exists_common_physical_error_constant (d N W M : ℕ) (η : ℝ)
    {Kr Cm Ccover Binput : ℝ} (hKr : 0 ≤ Kr) (hCm : 0 ≤ Cm)
    (hCc : 0 ≤ Ccover) (hBi : 0 ≤ Binput) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : RegCpl, ∀ δ D : ℝ, 0 ≤ δ → 0 ≤ D →
      ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
        (ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
          ((1+2*Real.pi)*(Kr*δ)^Q.links.length*spectralFrequencyLoss Q)) *
          (ENNReal.ofReal D*ENNReal.ofReal Cm^Q.links.length) *
          (ENNReal.ofReal (Ccover^Q.links.length)*
            ENNReal.ofReal (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^(2*Q.links.length+1))) ≤
      ENNReal.ofReal (C*(C*δ)^Q.links.length*D) := by
  let H := ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff
  have hH : H < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (timeFourierNorm_unitSquareCutoff_lt_top η)
  have hHreal : 0 ≤ H.toReal := ENNReal.toReal_nonneg
  let P := leafWeightedMomentLocalizationConstant d (N+1) M W*Binput
  have hP : 0 ≤ P := by
    unfold P leafWeightedMomentLocalizationConstant
    have hlocal := leafCellFourierMomentConstant_nonneg d (N+1) M
    have hs : 0 ≤ ∑' c : Fin d → ℤ, cellCenterWeight (M-W) c :=
      tsum_nonneg (cellCenterWeight_nonneg (M-W))
    exact mul_nonneg (mul_nonneg hlocal hs) hBi
  let a := maskedSourceSpatialConstant d 1 N W*(1+2*Real.pi)*P
  let b := ((2+Real.sqrt d)^(2*W))*Kr*(9*(1+4*Real.pi))*Cm*Ccover*P^2
  obtain ⟨C,hC,hbound⟩ := exists_common_geometric_bound (H.toReal*a) b
  refine ⟨C,hC,?_⟩
  intro Q δ D hδ hD
  let E := maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
    ((1+2*Real.pi)*Kr^Q.links.length*spectralFrequencyLoss Q) *
    Cm^Q.links.length*(Ccover^Q.links.length*P^(2*Q.links.length+1))
  have hmask : 0 ≤ maskedSourceSpatialConstant d (2*Q.links.length+1) N W := by
    unfold maskedSourceSpatialConstant
    have hroot := zero_le_one.trans (one_le_rootMaskDerivativeConstant d N)
    positivity
  have hrow : 0 ≤ spectralFrequencyLoss Q := by
    unfold spectralFrequencyLoss
    positivity
  have hpi : 0 ≤ 1+2*Real.pi := by positivity
  have heq :
      ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
        (ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
          ((1+2*Real.pi)*(Kr*δ)^Q.links.length*spectralFrequencyLoss Q)) *
          (ENNReal.ofReal D*ENNReal.ofReal Cm^Q.links.length) *
          (ENNReal.ofReal (Ccover^Q.links.length)*ENNReal.ofReal P^(2*Q.links.length+1))) =
      ENNReal.ofReal (H.toReal*E*δ^Q.links.length*D) := by
    rw [show ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff = ENNReal.ofReal H.toReal from
      (ENNReal.ofReal_toReal hH.ne).symm]
    dsimp only [E]
    simp only [mul_pow,mul_assoc]
    simp only [ENNReal.ofReal_mul hHreal,ENNReal.ofReal_mul hmask,
      ENNReal.ofReal_mul hpi,ENNReal.ofReal_mul (pow_nonneg hKr Q.links.length),
      ENNReal.ofReal_mul (pow_nonneg hδ Q.links.length),ENNReal.ofReal_mul hrow,
      ENNReal.ofReal_mul (pow_nonneg hCm Q.links.length),
      ENNReal.ofReal_mul (pow_nonneg hCc Q.links.length),
      ENNReal.ofReal_mul (pow_nonneg hP (2*Q.links.length+1)),
      ENNReal.ofReal_pow hKr,ENNReal.ofReal_pow hδ,
      ENNReal.ofReal_pow hCm,ENNReal.ofReal_pow hCc,ENNReal.ofReal_pow hP]
    ring
  change _ ≤ _
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  have hbudget : E ≤ a*b^Q.links.length := error_spatial_budget_le_geometric Q hKr hCm hCc hBi
  calc
    _ ≤ H.toReal*(a*b^Q.links.length)*δ^Q.links.length*D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbudget hHreal) (pow_nonneg hδ _)) hD
    _ = ((H.toReal*a)*b^Q.links.length)*δ^Q.links.length*D := by ring
    _ ≤ (C*C^Q.links.length)*δ^Q.links.length*D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hbound Q.links.length) (pow_nonneg hδ _)) hD
    _ = _ := by rw [mul_pow]; ring

end WaveTurbulence.RA1Leafwise
