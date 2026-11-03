/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!+# Radial Cauchy–Schwarz

Lemma 3 of `docs/research/git20-general-d.md`, in a form allowing any positive
radial weight. For the application take `f r = φ (k + r • θ)` and
`w r = (1 + ‖k + r • θ‖²)^(s/2)`.
The `MemLp` assumptions assert the finiteness of the two factors.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.WKEL2

/-- Radial Cauchy–Schwarz, with the two powers summing to `n-2`.
For spatial dimension `d`, set `n = (d : ℝ)`. -/
theorem radial_cauchy_schwarz (n : ℝ) (f w : ℝ → ℝ)
    (hf : ∀ r > 0, 0 ≤ f r) (hw : ∀ r > 0, 0 < w r)
    (h₁ : MemLp (fun r => f r * w r * r ^ ((n - 1) / 2)) 2
      (volume.restrict (Ioi 0)))
    (h₂ : MemLp (fun r => (w r)⁻¹ * r ^ ((n - 3) / 2)) 2
      (volume.restrict (Ioi 0))) :
    ∫ r in Ioi (0 : ℝ), f r * r ^ (n - 2) ≤
      Real.sqrt (∫ r in Ioi (0 : ℝ), (f r) ^ 2 * (w r) ^ 2 * r ^ (n - 1)) *
        Real.sqrt (∫ r in Ioi (0 : ℝ), ((w r)⁻¹) ^ 2 * r ^ (n - 3)) := by
  let u := fun r => f r * w r * r ^ ((n - 1) / 2)
  let v := fun r => (w r)⁻¹ * r ^ ((n - 3) / 2)
  have hu : 0 ≤ᵐ[volume.restrict (Ioi 0)] u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (mul_nonneg (hf r hr) (hw r hr).le) (Real.rpow_nonneg hr.le _)
  have hv : 0 ≤ᵐ[volume.restrict (Ioi 0)] v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (inv_nonneg.mpr (hw r hr).le) (Real.rpow_nonneg hr.le _)
  have hc : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hc hu hv
    (by simpa only [ENNReal.ofReal_ofNat] using h₁)
    (by simpa only [ENNReal.ofReal_ofNat] using h₂)
  have hp : (fun r => u r * v r) =ᵐ[volume.restrict (Ioi 0)]
      (fun r => f r * r ^ (n - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp only [u, v]
    calc
      _ = f r * (w r * (w r)⁻¹) *
          (r ^ ((n - 1) / 2) * r ^ ((n - 3) / 2)) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ (hw r hr).ne', mul_one, ← Real.rpow_add hr]
        congr 2
        ring
  have he : (fun r => u r ^ (2 : ℝ)) =ᵐ[volume.restrict (Ioi 0)]
      (fun r => (f r) ^ 2 * (w r) ^ 2 * r ^ (n - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp only [u]
    rw [Real.rpow_two, mul_pow, mul_pow, ← Real.rpow_mul_natCast hr.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (n - 1) / 2 * (2 : ℝ) = n - 1 by ring]
  have ha : (fun r => v r ^ (2 : ℝ)) =ᵐ[volume.restrict (Ioi 0)]
      (fun r => ((w r)⁻¹) ^ 2 * r ^ (n - 3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp only [v]
    rw [Real.rpow_two, mul_pow, ← Real.rpow_mul_natCast hr.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (n - 3) / 2 * (2 : ℝ) = n - 3 by ring]
  rw [integral_congr_ae hp, integral_congr_ae he, integral_congr_ae ha] at h
  simpa only [one_div, invOf_eq_inv, Real.sqrt_eq_rpow] using h

end WaveTurbulence.WKEL2
