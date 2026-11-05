/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeadingGeometricBudget
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalErrorSpatial

/-! # Explicit geometric order dependence of the full physical error bound -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Incoh WaveTurbulence.Fourier

/-- The full physical error's spatial constants are geometric; the row
loss is the actual checked C2 loss and each leaf pays its own input norm. -/
theorem error_spatial_budget_le_geometric {d N W M : ℕ} (Q : RegCpl)
    {r Cm Ccover Binput : ℝ} (hr : 0 ≤ r) (hCm : 0 ≤ Cm)
    (hCc : 0 ≤ Ccover) (hBi : 0 ≤ Binput) :
    maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
      ((1+2*Real.pi)*r^Q.links.length*spectralFrequencyLoss Q) *
      Cm^Q.links.length *
      (Ccover^Q.links.length*
        (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^(2*Q.links.length+1)) ≤
      (maskedSourceSpatialConstant d 1 N W*(1+2*Real.pi)*
        (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)) *
      (((2+Real.sqrt d)^(2*W))*r*(9*(1+4*Real.pi))*Cm*Ccover*
        (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^2)^Q.links.length := by
  have hMask : 0 ≤ maskedSourceSpatialConstant d (2*Q.links.length+1) N W := by
    unfold maskedSourceSpatialConstant
    have hroot := zero_le_one.trans (one_le_rootMaskDerivativeConstant d N)
    positivity
  have hleaf : 0 ≤ leafWeightedMomentLocalizationConstant d (N+1) M W*Binput := by
    unfold leafWeightedMomentLocalizationConstant
    have hlocal := leafCellFourierMomentConstant_nonneg d (N+1) M
    have hs : 0 ≤ ∑' c : Fin d → ℤ, cellCenterWeight (M-W) c :=
      tsum_nonneg (cellCenterWeight_nonneg (M-W))
    exact mul_nonneg (mul_nonneg hlocal hs) hBi
  calc
    _ ≤ maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
        ((1+2*Real.pi)*r^Q.links.length*(9*(1+4*Real.pi))^Q.links.length) *
        Cm^Q.links.length *
        (Ccover^Q.links.length*
          (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^(2*Q.links.length+1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hMask
      exact mul_le_mul_of_nonneg_left (spectralFrequencyLoss_le_geometric Q) (by positivity)
    _ = _ := by
      rw [maskedSourceSpatialConstant_halfOrder]
      simp only [mul_pow,pow_add,pow_one,pow_mul]
      ring

end WaveTurbulence.RegAsymp
