/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentSmallParameters
/-! The already chosen coherent delta threshold also pays the incoherent low-norm cost. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem incoherent_smallness_of_coherent (P : WTParams) (hC : 1 ≤ P.C₁)
    (hs : CoherentSmallParameters P) :
    (2 * P.C₁ * P.C₁) * ((12 ^ 9 : ℝ) * 32 * P.C₁ * P.C₁ ^ 2 * P.δ) ≤ Real.sqrt P.δ := by
  have hδ := hs.delta_pos
  have hc0 : 0 < P.C₁ := by linarith
  have hbase : (2 * P.C₁ * P.C₁) * ((12 ^ 9 : ℝ) * 32 * P.C₁ * P.C₁ ^ 2 * P.δ) ≤
      (P.C₁ + P.C₁ ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * P.C₁ ^ 2) *
        (2 * P.C₁ ^ 2 * P.δ)) := by
    have hh := mul_nonneg (sq_nonneg P.C₁)
      (show 0 ≤ 64 * (12 ^ 9 : ℝ) * P.C₁ ^ 4 * P.δ by positivity)
    norm_num
    nlinarith
  have he : Real.exp (-1 : ℝ) ≤ 1 := by simpa using Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
  exact (hbase.trans hs.tail_delta).trans (mul_le_of_le_one_right (Real.sqrt_nonneg _) he)

end WaveTurbulence.LGSpine
