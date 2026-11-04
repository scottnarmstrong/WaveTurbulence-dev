/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootCutoff

/-! # An actual smooth cutoff covering a finite source layer range -/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- A smooth cutoff equal to one on the entire finite source clock range. -/
@[expose] def finiteLayerCutoff (D : ℕ) (t : ℝ) : ℝ := rootCutoff (t / ((D : ℝ) + 2))

@[fun_prop] theorem contDiff_finiteLayerCutoff (D : ℕ) : ContDiff ℝ ∞ (finiteLayerCutoff D) :=
  contDiff_rootCutoff.comp (by fun_prop)

theorem hasCompactSupport_finiteLayerCutoff (D : ℕ) : HasCompactSupport (finiteLayerCutoff D) := by
  have hs : (D : ℝ) + 2 ≠ 0 := by positivity
  have h := hasCompactSupport_rootCutoff.comp_homeomorph (Homeomorph.mulLeft₀
    (((D : ℝ) + 2)⁻¹) (inv_ne_zero hs))
  convert h using 1
  funext t
  change rootCutoff (t / ((D : ℝ) + 2)) = rootCutoff (((D : ℝ) + 2)⁻¹ * t)
  rw [div_eq_mul_inv, mul_comm]

/-- The cutoff is exactly one on the required closed range, including external boundaries. -/
theorem finiteLayerCutoff_eq_one (D : ℕ) {t : ℝ} (ht : |t| ≤ (D : ℝ) + 2) :
    finiteLayerCutoff D t = 1 := by
  apply rootCutoff_eq_one
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (D : ℝ) + 2)]
  exact (div_le_one (by positivity : (0 : ℝ) < (D : ℝ) + 2)).2 ht

end WaveTurbulence.Incoh
