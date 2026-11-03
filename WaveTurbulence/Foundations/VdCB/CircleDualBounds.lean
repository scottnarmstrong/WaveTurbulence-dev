/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleDualCalculus

/-!
# Uniform fifth-derivative bounds on circle dual blocks

On `Y≤ν≤2Y` with `Y≥h>0`, the dual phase has fifth derivative comparable
to `Rh²/Y⁶`, with absolute constants. Thus the circle's full octant range
is handled without a small multiplicative-perturbation assumption.
-/

public section

namespace WaveTurbulence.VdCB

private theorem circle_denominator_bounds {h Y x : ℝ} (hh : 0 < h) (hY : h ≤ Y)
    (hx : x ∈ Set.Icc Y (2 * Y)) :
    Y ^ 9 ≤ (h ^ 2 + x ^ 2) ^ 4 * Real.sqrt (h ^ 2 + x ^ 2) ∧
      (h ^ 2 + x ^ 2) ^ 4 * Real.sqrt (h ^ 2 + x ^ 2) ≤ 1875 * Y ^ 9 := by
  have hY0 := hh.trans_le hY
  have hx0 := hY0.trans_le hx.1
  have hD : 0 < h ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)
  have hlo : Y ^ 2 ≤ h ^ 2 + x ^ 2 := by nlinarith only [hY0.le, hx.1, sq_nonneg h]
  have hhi : h ^ 2 + x ^ 2 ≤ 5 * Y ^ 2 := by nlinarith only [hh.le, hY, hx0.le, hx.2, hY0.le]
  have hs := Real.sq_sqrt hD.le
  have hs0 := Real.sqrt_nonneg (h ^ 2 + x ^ 2)
  have hslo : Y ≤ Real.sqrt (h ^ 2 + x ^ 2) := by nlinarith only [hlo, hs, hs0, hY0.le]
  have hshi : Real.sqrt (h ^ 2 + x ^ 2) ≤ 3 * Y := by nlinarith only [hhi, hs, hs0, hY0.le]
  have hpLo := pow_le_pow_left₀ (sq_nonneg Y) hlo 4
  have hpHi := pow_le_pow_left₀ hD.le hhi 4
  constructor
  · convert mul_le_mul hpLo hslo hY0.le (by positivity : 0 ≤ (h ^ 2 + x ^ 2) ^ 4) using 1; ring
  · convert mul_le_mul hpHi hshi hs0 (by positivity : 0 ≤ (5 * Y ^ 2) ^ 4) using 1; ring

/-- Explicit comparison constants for the fifth derivative of the circle
Legendre phase on every dyadic block in the octant dual range. -/
theorem abs_iteratedDeriv_five_circleDualPhase_bounds {R h Y x : ℝ} (hR : 0 < R)
    (hh : 0 < h) (hY : h ≤ Y) (hx : x ∈ Set.Icc Y (2 * Y)) :
    R * h ^ 2 / (125 * Y ^ 6) ≤ |iteratedDeriv 5 (circleDualPhase R h) x| ∧
      |iteratedDeriv 5 (circleDualPhase R h) x| ≤ 480 * R * h ^ 2 / Y ^ 6 := by
  have hY0 := hh.trans_le hY
  have hx0 := hY0.trans_le hx.1
  have hD : 0 < h ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)
  let den : ℝ := (h ^ 2 + x ^ 2) ^ 4 * Real.sqrt (h ^ 2 + x ^ 2)
  let num : ℝ := 15 * R * h ^ 2 * x * (4 * x ^ 2 - 3 * h ^ 2)
  have hd0 : 0 < den := mul_pos (pow_pos hD 4) (Real.sqrt_pos.mpr hD)
  have hden := circle_denominator_bounds hh hY hx
  have hcoreLo : Y ^ 2 ≤ 4 * x ^ 2 - 3 * h ^ 2 := by
    nlinarith only [hh.le, hY, hY0.le, hx.1, hx0.le]
  have hcoreHi : 4 * x ^ 2 - 3 * h ^ 2 ≤ 16 * Y ^ 2 := by
    nlinarith only [hx0.le, hx.2, hY0.le, sq_nonneg h]
  have hnLo : 15 * R * h ^ 2 * Y ^ 3 ≤ num := by
    have hp := mul_le_mul hx.1 hcoreLo (sq_nonneg Y) hx0.le
    have ht := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 15 * R * h ^ 2)
    convert ht using 1
    · ring
    · dsimp only [num]
      ring
  have hnHi : num ≤ 480 * R * h ^ 2 * Y ^ 3 := by
    have hp := mul_le_mul hx.2 hcoreHi (le_trans (sq_nonneg Y) hcoreLo) (by positivity : 0 ≤ 2 * Y)
    have ht := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 15 * R * h ^ 2)
    convert ht using 1
    · dsimp only [num]
      ring
    · ring
  have hpow : (h ^ 2 + x ^ 2) ^ (9 / 2 : ℝ) = den := by
    rw [show (9 / 2 : ℝ) = 4 + 1 / 2 by ring, Real.rpow_add hD, Real.rpow_ofNat _ 4,
      ← Real.sqrt_eq_rpow]
  have habs : |iteratedDeriv 5 (circleDualPhase R h) x| = num / den := by
    rw [iteratedDeriv_five_circleDualPhase R hh]
    unfold circleDualFifth
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 15 * R * h ^ 2 * x),
      abs_of_nonpos (by linarith only [hcoreLo, sq_nonneg Y] : 3 * h ^ 2 - 4 * x ^ 2 ≤ 0),
      abs_of_pos (Real.rpow_pos_of_pos hD _), Real.rpow_neg hD.le, hpow]
    dsimp only [num]
    rw [div_eq_mul_inv]
    ring
  rw [habs]
  constructor
  · apply (div_le_div_iff₀ (by positivity : 0 < 125 * Y ^ 6) hd0).mpr
    calc
      _ ≤ R * h ^ 2 * (1875 * Y ^ 9) := mul_le_mul_of_nonneg_left hden.2 (by positivity)
      _ = (15 * R * h ^ 2 * Y ^ 3) * (125 * Y ^ 6) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hnLo (by positivity)
  · apply (div_le_div_iff₀ hd0 (pow_pos hY0 6)).mpr
    calc
      _ ≤ (480 * R * h ^ 2 * Y ^ 3) * Y ^ 6 := mul_le_mul_of_nonneg_right hnHi (by positivity)
      _ = (480 * R * h ^ 2) * Y ^ 9 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden.1 (by positivity)

end WaveTurbulence.VdCB
