/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SmallParameterConditions
public import WaveTurbulence.Foundations.SumintPar.IncoherenceInterpolationMargin

/-!
# Exact source exponent assembly after interpolation and restoration

Only two partition powers are spent by the explicit extension. The
proved twelve-power reserve leaves the required half allowance for the
step-dependent compact multiplier constant.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.SumintPar

/-- The restored interpolated exponent is bounded by the exact drafted exponent. -/
theorem source_restored_exponent_le {d : ℕ} (D : SumintDatum d) {γ η : ℝ}
    (hη : SumintSmallness d γ η) :
    (D.S.M:ℝ)*((d:ℝ)-γ)-
      (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
      (1-interpolationWeight η)*(partitionExponent η/20)*(D.M₀:ℝ)+
      14*(d:ℝ)*interpolationWeight η+2*partitionExponent η+η^7/2 ≤
    (D.S.M:ℝ)*((d:ℝ)-γ)-
      η^2*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
      η^8*(D.M₀:ℝ)+η^7 := by
  have hloss := partition_interpolation_loss_le_half hη.eta_pos.le hη.eight_lt.le hη.half_loss
  have hβ := (partitionExponent_pos hη.eta_pos).le
  have hbad := mul_le_mul_of_nonneg_right hη.square_gain
    (show 0 ≤ ((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ) by positivity)
  have hinc := mul_le_mul_of_nonneg_right
    (incoherence_gain_after_interpolation hη.eta_pos.le hη.twentyfour_le hη.sqrt_forty)
    (Nat.cast_nonneg D.M₀)
  nlinarith only [hloss,hβ,hbad,hinc]

end WaveTurbulence.SumintPar
