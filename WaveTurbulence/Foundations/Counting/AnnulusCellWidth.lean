/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Choice of the short annulus cell width

For radius `r³`, the scale `1 / (10000 * (1/r + rho))` simultaneously
controls the area due to the annulus width and the circular curvature.
This is the Cartesian counterpart of the angular subdivision in DH23
`basiccount0pre` (1), elementary branch.
-/

public section

namespace WaveTurbulence.Counting

/-- An explicit positive cell width satisfying the thin-triangle condition
and an exact reciprocal formula for the covering count. -/
theorem exists_annulus_cell_width {r rho : ℝ} (hr : 0 < r) (hrho : 0 ≤ rho) :
    ∃ T : ℝ, 0 < T ∧ 2*T*(1000*(rho+T^2/r^3)) < 1 ∧
      1/T = 10000*(1/r+rho) := by
  let T : ℝ := 1/(10000*(1/r+rho))
  have hD : 0 < 1/r+rho := add_pos_of_pos_of_nonneg (one_div_pos.mpr hr) hrho
  have hT : 0 < T := by dsimp only [T]; positivity
  have he : T*(1/r+rho) = 1/10000 := by dsimp only [T]; field_simp
  have hprod : T*rho ≤ 1/10000 := by
    have hp := mul_nonneg hT.le (one_div_pos.mpr hr).le
    nlinarith only [he,hp]
  have hquot : T/r ≤ 1/10000 := by
    have hp := mul_nonneg hT.le hrho
    rw [div_eq_mul_one_div]
    nlinarith only [he,hp]
  have hcap : T ≤ r/10000 := by
    have hh := (div_le_iff₀ hr).mp hquot
    linarith only [hh]
  have hpow := pow_le_pow_left₀ hT.le hcap 3
  have hcube : T^3/r^3 ≤ 1/10000 := by
    apply (div_le_iff₀ (pow_pos hr 3)).mpr
    have hp := pow_nonneg hr.le 3
    nlinarith only [hpow,hp]
  refine ⟨T,hT,?_,?_⟩
  · have hid : 2*T*(1000*(rho+T^2/r^3)) = 2000*(T*rho+T^3/r^3) := by ring
    rw [hid]
    linarith only [hprod,hcube]
  · dsimp only [T]
    field_simp

end WaveTurbulence.Counting
