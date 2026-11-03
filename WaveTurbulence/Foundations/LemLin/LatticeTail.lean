/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Torus.Inversion
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Uniform shifted scalar lattice tails

A summable majorant for the frequency tails in TARGET `lemcubic0`. The
lattice spacing is bounded below, while the shift is entirely unrestricted.
-/

public section

namespace WaveTurbulence.LemLin

/-- The elementary weight used to dominate frequency sums. -/
@[expose] noncomputable def scalarTailWeight (x : ℝ) : ℝ := ((1 + |x|) ^ 2)⁻¹

theorem scalarTailWeight_nonneg (x : ℝ) : 0 ≤ scalarTailWeight x := by
  unfold scalarTailWeight
  positivity

/-- Recentered lattice points with spacing at least `1/3` have a uniform tail. -/
theorem scalarTailWeight_recenter {w b : ℝ} (hw : 1 / 3 ≤ w)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k : ℤ) :
    scalarTailWeight (w * ((k : ℝ) - b)) ≤ 36 * scalarTailWeight k := by
  have htri : |(k : ℝ)| ≤ |(k : ℝ) - b| + 1 := by
    have h := abs_add_le ((k : ℝ) - b) b
    rw [sub_add_cancel, abs_of_nonneg hb0] at h
    linarith only [h, hb1]
  have hw0 : 0 ≤ w := by linarith
  have hscale : 1 + |(k : ℝ)| ≤ 6 * (1 + |w * ((k : ℝ) - b)|) := by
    rw [abs_mul, abs_of_nonneg hw0]
    nlinarith only [htri, hw, abs_nonneg ((k : ℝ) - b)]
  have hp : 0 < 1 + |(k : ℝ)| := by positivity
  have hq : 0 < 1 + |w * ((k : ℝ) - b)| := by positivity
  have hsq := (sq_le_sq₀ hp.le (by positivity)).mpr hscale
  simp only [scalarTailWeight, ← one_div]
  rw [mul_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hq) (sq_pos_of_pos hp)).mpr
  nlinarith only [hsq]

/-- A fixed finite constant for all scalar shifted lattice tails. -/
@[expose] noncomputable def scalarTailConstant : ℝ :=
  36 * ∑' k : ℤ, scalarTailWeight k

theorem scalarTailConstant_nonneg : 0 ≤ scalarTailConstant := by
  unfold scalarTailConstant
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun k : ℤ => scalarTailWeight_nonneg k))

/-- Summability and a uniform bound, including arbitrary frequency shifts. -/
theorem scalar_lattice_tail {w : ℝ} (hw : 1 / 3 ≤ w) (a : ℝ) :
    Summable (fun k : ℤ => scalarTailWeight (w * k + a)) ∧
      (∑' k : ℤ, scalarTailWeight (w * k + a)) ≤ scalarTailConstant := by
  have hwpos : 0 < w := by linarith
  let n : ℤ := ⌊-a / w⌋
  let b : ℝ := Int.fract (-a / w)
  have hb0 : 0 ≤ b := Int.fract_nonneg _
  have hb1 : b ≤ 1 := (Int.fract_lt_one _).le
  have hrecenter (k : ℤ) : w * ((k + n : ℤ) : ℝ) + a = w * ((k : ℝ) - b) := by
    have he : (n : ℝ) + b = -a / w := Int.floor_add_fract _
    push_cast
    have he' : w * ((n : ℝ) + b) = -a := by
      rw [he]
      field_simp [hwpos.ne']
    nlinarith only [he']
  have hg : Summable (fun k : ℤ => 36 * scalarTailWeight k) :=
    summable_inv_one_add_abs_int_sq.mul_left 36
  have hbound (k : ℤ) : scalarTailWeight (w * ((k + n : ℤ) : ℝ) + a) ≤
      36 * scalarTailWeight k := by
    rw [hrecenter]
    exact scalarTailWeight_recenter hw hb0 hb1 k
  have hs : Summable (fun k : ℤ => scalarTailWeight (w * ((k + n : ℤ) : ℝ) + a)) :=
    Summable.of_nonneg_of_le (fun k => scalarTailWeight_nonneg _) hbound hg
  have hs' : Summable (fun k : ℤ => scalarTailWeight (w * k + a)) :=
    (Equiv.addRight n).summable_iff.mp hs
  refine ⟨hs', ?_⟩
  calc
    _ = ∑' k : ℤ, scalarTailWeight (w * ((k + n : ℤ) : ℝ) + a) :=
      ((Equiv.addRight n).tsum_eq _).symm
    _ ≤ ∑' k : ℤ, 36 * scalarTailWeight k := hs.tsum_le_tsum hbound hg
    _ = scalarTailConstant := tsum_mul_left

end WaveTurbulence.LemLin
