/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeadingSpatialIdentification
public import WaveTurbulence.Foundations.Spine.RA1LW.SpectralOrderLoss

/-! # The actual source singular spatial bound has geometric order dependence -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Incoh

/-- The literal mask scale has exact geometric leaf-count dependence. -/
theorem maskedSourceSpatialConstant_halfOrder (d n N W : ℕ) :
    maskedSourceSpatialConstant d (2*n+1) N W =
      maskedSourceSpatialConstant d 1 N W * ((2+Real.sqrt d)^(2*W))^n := by
  unfold maskedSourceSpatialConstant
  simp only [pow_add,pow_one,mul_pow,pow_mul]
  ring

/-- All explicit spatial and singular constants combine geometrically;
the only nonconstant row loss is controlled by the proved C2 estimate. -/
theorem leading_spatial_budget_le_geometric {d N W M : ℕ} (Q : RegCpl)
    {Mcell Ccover Binput : ℝ} (hMc : 0 ≤ Mcell) (hCc : 0 ≤ Ccover) (hBi : 0 ≤ Binput) :
    maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
      ((1+2*Real.pi)*
        ((((2*max 1 (Real.sqrt d)+5)^(2*d))^Q.links.length*Mcell^Q.links.length*
          halfLinkFirstMomentConstant d^(2*Q.links.length))*spectralFrequencyLoss Q)) *
      (Ccover^Q.links.length*
        (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^(2*Q.links.length+1)) ≤
      (maskedSourceSpatialConstant d 1 N W*(1+2*Real.pi)*
        (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)) *
      (((2+Real.sqrt d)^(2*W))*((2*max 1 (Real.sqrt d)+5)^(2*d))*Mcell*
        (halfLinkFirstMomentConstant d)^2*(9*(1+4*Real.pi))*Ccover*
        (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^2)^Q.links.length := by
  have hD := (halfLinkFirstMomentConstant_pos d).le
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
  have hrow := spectralFrequencyLoss_le_geometric Q
  calc
    _ ≤ maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
      ((1+2*Real.pi)*
        ((((2*max 1 (Real.sqrt d)+5)^(2*d))^Q.links.length*Mcell^Q.links.length*
          halfLinkFirstMomentConstant d^(2*Q.links.length))*(9*(1+4*Real.pi))^Q.links.length)) *
      (Ccover^Q.links.length*
        (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^(2*Q.links.length+1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hMask
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = _ := by
      rw [maskedSourceSpatialConstant_halfOrder]
      simp only [mul_pow,pow_add,pow_one,pow_mul]
      ring

/-- A common geometric constant can absorb a fixed prefactor, including order zero. -/
theorem exists_common_geometric_bound (a b : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, a*b^n ≤ C*C^n := by
  let C := max 1 (max |a| |b|)
  have hC : 1 ≤ C := le_max_left _ _
  have ha : |a| ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hb : |b| ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro n
  calc
    a*b^n ≤ |a*b^n| := le_abs_self _
    _ = |a| * |b|^n := by rw [abs_mul,abs_pow]
    _ ≤ C*C^n := mul_le_mul ha (pow_le_pow_left₀ (abs_nonneg _) hb n)
      (pow_nonneg (abs_nonneg _) _) (zero_le_one.trans hC)

end WaveTurbulence.RA1Leafwise
