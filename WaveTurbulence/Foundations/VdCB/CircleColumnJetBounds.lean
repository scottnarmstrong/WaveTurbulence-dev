/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleColumnLocalization
public import WaveTurbulence.Foundations.VdCB.CircleFrequencyBounds

/-!
# Actual translated-column derivative bounds

The global representative has the exact source derivative scales on the
physical column block, uniformly in its arbitrary real center.
-/

public section

open Set

namespace WaveTurbulence.VdCB

/-- Curvature and cubic derivative bounds for the actual column representative. -/
theorem circleColumnExtension_curvature_bounds {R h U c x : ℝ}
    (hU : 0 < U) (hUR : 3 * U ≤ R) (hh : 0 < h)
    (hx : R + c - x ∈ Icc U (2 * U)) :
    (h * R ^ 2 * (4 * R * U) ^ (-(3 / 2) : ℝ) ≤
        -deriv (deriv (circleColumnExtension R h U hU c)) x ∧
      -deriv (deriv (circleColumnExtension R h U hU c)) x ≤
        h * R ^ 2 * (R * U) ^ (-(3 / 2) : ℝ)) ∧
      |iteratedDeriv 3 (circleColumnExtension R h U hU c) x| ≤
        3 * h * R ^ 3 * (R * U) ^ (-(5 / 2) : ℝ) := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have huarc : R + c - x ∈ Ioo 0 R := ⟨hU.trans_le hx.1, by linarith [hx.2]⟩
  constructor
  · rw [deriv_deriv_circleColumnExtension hU hR hx hUR,
      ← deriv_deriv_circlePhase hR huarc]
    exact neg_deriv_deriv_circlePhase_bounds hU hUR hh hx
  · rw [abs_iteratedDeriv_three_circleColumnExtension hU hx]
    exact abs_iteratedDeriv_three_circlePhase_le hU hUR hh hx

/-- The actual translated-column frequency has the source dyadic scale. -/
theorem circleColumnExtension_frequency_bounds {R h U c x : ℝ}
    (hU : 0 < U) (hUR : 6 * U ≤ R) (hh : 0 < h)
    (hx : R + c - x ∈ Icc U (2 * U)) :
    0 < -deriv (circleColumnExtension R h U hU c) x ∧
      h ^ 2 * R / (9 * U) ≤ (-deriv (circleColumnExtension R h U hU c) x) ^ 2 ∧
      (-deriv (circleColumnExtension R h U hU c) x) ^ 2 ≤ h ^ 2 * R / U := by
  have hR : 0 < R := (by positivity : 0 < 6 * U).trans_le hUR
  have hUR3 : 3 * U ≤ R := by linarith only [hUR, hU]
  rw [deriv_circleColumnExtension hU hR hx hUR3, neg_neg]
  exact ⟨circleSourceFirst_pos hR hh ⟨hU.trans_le hx.1, by linarith [hx.2]⟩,
    circleSourceFirst_sq_bounds hU hUR hx⟩

/-- A source interval contained in the physical block stays in the local
representative's agreement region, including both endpoints. -/
theorem column_interval_reflection_mem {R U c a b x : ℝ}
    (ha : R + c - 2 * U ≤ a) (hb : b ≤ R + c - U) (hx : x ∈ Icc a b) :
    R + c - x ∈ Icc U (2 * U) := by constructor <;> linarith [hx.1, hx.2]

end WaveTurbulence.VdCB
