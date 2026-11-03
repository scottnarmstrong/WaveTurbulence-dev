/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AxisTransverseFar

/-!
# The complete far field of the anisotropic kernel

The remaining cylindrical region has scalar radius at least one and transverse
radius below one, so Hölder powers are integrable exactly for `1 < p < n`.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {n : ℕ}

/-- Scalar-coordinate bound away from the scalar origin. -/
theorem axisKernel_le_scalar_product (p : ℝ) (hp : 0 ≤ p)
    {z : ℝ × Mom n} (ht : z.1 ≠ 0) :
    axisKernel p z ≤ |z.1| ^ (-p) * ‖z.2‖ ^ (-p) := by
  have ht0 : 0 < |z.1| := abs_pos.mpr ht
  have h : (z.1 ^ 2 + ‖z.2‖ ^ 2) ^ (-p / 2) ≤ (z.1 ^ 2) ^ (-p / 2) :=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero ht)
      (le_add_of_nonneg_right (sq_nonneg ‖z.2‖)) (by linarith only [hp])
  have he : (z.1 ^ 2) ^ (-p / 2) = |z.1| ^ (-p) := by
    rw [← sq_abs z.1, ← Real.rpow_natCast |z.1| 2, ← Real.rpow_mul ht0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-p / 2) = -p by ring]
  rw [he] at h
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (norm_nonneg _) _)

/-- Integrability of the p-th kernel on the cylindrical far field. -/
theorem integrable_axisKernel_far (hn : 2 ≤ n) (p : ℝ) (hp : 1 < p)
    (hpn : p < n) (hdim : (n : ℝ) + 1 < 2 * p) :
    Integrable ((ball (0 : ℝ × Mom n) 1)ᶜ.indicator (axisKernel p)) (volume.prod volume) := by
  have hiT := (integrableOn_exterior_norm_neg_rpow (volume : Measure ℝ) p
    (by simpa using hp) 1 zero_lt_one).integrable_indicator measurableSet_ball.compl
  have hiW := (integrableOn_ball_norm_neg_rpow (volume : Measure (Mom n))
    (by rw [finrank_euclideanSpace_fin]; omega) p
    (by simpa only [finrank_euclideanSpace_fin] using hpn) 1).integrable_indicator measurableSet_ball
  have hiProd := hiT.mul_prod hiW
  have hiRad := integrable_axisKernel_transverse_far (n := n) p hp hdim
  refine (hiRad.add hiProd).mono'
    ((measurable_axisKernel p).indicator measurableSet_ball.compl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (indicator_nonneg (fun x _ => axisKernel_nonneg p x) z)]
  simp only [Pi.add_apply]
  by_cases hball : z ∈ ball (0 : ℝ × Mom n) 1
  · rw [indicator_of_notMem (show z ∉ (ball (0 : ℝ × Mom n) 1)ᶜ from fun h => h hball)]
    exact add_nonneg (by split_ifs; exact axisKernel_nonneg _ _; exact le_refl 0)
      (mul_nonneg (indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _)
        (indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _))
  · rw [indicator_of_mem hball]
    by_cases hw : 1 ≤ ‖z.2‖
    · simp only [hw, ↓reduceIte]
      exact le_add_of_nonneg_right
        (mul_nonneg (indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _)
          (indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _))
    · simp only [hw, ↓reduceIte, zero_add]
      have hwlt : ‖z.2‖ < 1 := lt_of_not_ge hw
      have htge : 1 ≤ ‖z.1‖ := by
        have h := le_of_not_gt (show ¬‖z‖ < 1 by simpa only [mem_ball_zero_iff] using hball)
        rw [Prod.norm_def] at h
        exact le_of_not_gt fun ht => (not_lt_of_ge h) (max_lt ht hwlt)
      have htmem : z.1 ∈ (ball (0 : ℝ) 1)ᶜ := by
        simpa only [mem_compl_iff, mem_ball_zero_iff, not_lt] using htge
      have hwmem : z.2 ∈ ball (0 : Mom n) 1 := mem_ball_zero_iff.mpr hwlt
      rw [indicator_of_mem htmem, indicator_of_mem hwmem, Real.norm_eq_abs]
      exact axisKernel_le_scalar_product p (zero_le_one.trans hp.le) (by
        intro h
        simp only [h, norm_zero] at htge
        linarith only [htge])

/-- Kernel powers agree with taking the p-th power of the base kernel. -/
theorem axisKernel_one_rpow (p : ℝ) (z : ℝ × Mom n) :
    (axisKernel 1 z) ^ p = axisKernel p z := by
  rw [axisKernel, Real.mul_rpow (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (norm_nonneg _),
    show (-(1 : ℝ) / 2) * p = -p / 2 by ring,
    show (-(1 : ℝ)) * p = -p by ring]
  rfl

/-- Far-field Lᵖ membership in the exact exponent window for M₁. -/
theorem memLp_axisKernel_far (hn : 2 ≤ n) (p : ℝ)
    (hlo : (n : ℝ) + 1 < 2 * p) (hhi : p < n) :
    MemLp ((ball (0 : ℝ × Mom n) 1)ᶜ.indicator (axisKernel 1))
      (ENNReal.ofReal p) (volume.prod volume) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 < p := by linarith only [hlo, hnR]
  have hm : AEStronglyMeasurable
      ((ball (0 : ℝ × Mom n) 1)ᶜ.indicator (axisKernel 1)) (volume.prod volume) :=
    ((measurable_axisKernel (n := n) 1).indicator measurableSet_ball.compl).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (ne_of_gt (ENNReal.ofReal_pos.mpr (zero_lt_one.trans hp)))
    ENNReal.ofReal_ne_top).mp
  have hi := integrable_axisKernel_far hn p hp hhi hlo
  convert hi using 1
  funext z
  rw [ENNReal.toReal_ofReal (zero_le_one.trans hp.le)]
  by_cases hball : z ∈ (ball (0 : ℝ × Mom n) 1)ᶜ
  · rw [indicator_of_mem hball, indicator_of_mem hball,
      Real.norm_of_nonneg (axisKernel_nonneg 1 z), axisKernel_one_rpow]
  · simp only [indicator_of_notMem hball, norm_zero,
      Real.zero_rpow (zero_lt_one.trans hp).ne']

end WaveTurbulence.WKEL2
