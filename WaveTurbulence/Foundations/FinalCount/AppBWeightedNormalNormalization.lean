/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBNormalNormalization
import Mathlib.Tactic

/-! # Exact cancellation of a lost ladder weight in a normal double-pair removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal

/-- Conditional scalar assembly helper. The inverse counting weight
cancels the one lost link weight exactly, with no logarithmic loss. -/
theorem appb_normal_normalization_of_raw_inverse_weight (Epre Epos : ℝ≥0∞) (χ : ℤ)
    (L D δ C1 C X H : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hC1 : 1 ≤ C1)
    (hC : C ≤ C1) (hC0 : 0 ≤ C) (hX : 0 < X)
    (hraw : Epre ≤ ENNReal.ofReal (C*δ⁻¹*L^(2*D)*X⁻¹)*Epos) :
    Epre*ENNReal.ofReal (L^(-D*((χ+2 : ℤ) : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^(χ+2)*(X*H)) ≤
      Epos*ENNReal.ofReal (L^(-D*(χ : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^χ*H) := by
  have hA : 0 ≤ C*δ⁻¹*L^(2*D) := by positivity
  have hAX : 0 ≤ C*δ⁻¹*L^(2*D)*X⁻¹ := mul_nonneg hA (inv_nonneg.mpr hX.le)
  have hrawX : Epre*ENNReal.ofReal X ≤ ENNReal.ofReal (C*δ⁻¹*L^(2*D))*Epos := by
    calc
      _ ≤ (ENNReal.ofReal (C*δ⁻¹*L^(2*D)*X⁻¹)*Epos)*ENNReal.ofReal X := mul_le_mul_left hraw _
      _ = (ENNReal.ofReal (C*δ⁻¹*L^(2*D)*X⁻¹)*ENNReal.ofReal X)*Epos := by ring
      _ = _ := by
        rw [← ENNReal.ofReal_mul hAX,mul_assoc,inv_mul_cancel₀ hX.ne',mul_one]
  have hn := appb_normal_normalization_of_raw (Epre*ENNReal.ofReal X) Epos χ L D δ C1 C H
    hL hδ hC1 hC hC0 hrawX
  calc
    _ = (Epre*ENNReal.ofReal X)*
        ENNReal.ofReal (L^(-D*((χ+2 : ℤ) : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^(χ+2)*H) := by
      rw [show L^(-D*((χ+2 : ℤ) : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^(χ+2)*(X*H) =
        X*(L^(-D*((χ+2 : ℤ) : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^(χ+2)*H) by ring,
        ENNReal.ofReal_mul hX.le]
      ring
    _ ≤ _ := hn

end WaveTurbulence.Mole
