/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.RadialCauchyENN
public import WaveTurbulence.Foundations.WKEL2.AngularCauchyAlgebra

/-!
# Weighted spatial Cauchy–Schwarz for nonnegative extended kernels
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The final spatial Cauchy–Schwarz step in research-note Proposition 6. -/
theorem lintegral_weighted_spatial_cauchy (s : ℝ) {f : Mom d → ℝ}
    (hf : Measurable f) (hLf : MemLp (weightedFunction s f) 2)
    {H : Mom d → ℝ≥0∞} (hH : Measurable H) (k : Mom d) :
    (∫⁻ w : Mom d, ENNReal.ofReal |f (k + w)| * H w) ≤
      ENNReal.ofReal (weightedL2Norm s f) *
        (∫⁻ w : Mom d, ENNReal.ofReal (japaneseDecay (2 * s) (k + w)) * (H w) ^ 2) ^
          ((1 : ℝ) / 2) := by
  let L : Mom d → ℝ≥0∞ := fun w => ENNReal.ofReal |weightedFunction s f (k + w)|
  let R : Mom d → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (((1 + ‖k + w‖ ^ 2) ^ (s / 2))⁻¹) * H w
  have hshift : Measurable (fun w : Mom d => k + w) := by fun_prop
  have hL : Measurable L := ((measurable_weightedFunction s hf).abs.ennreal_ofReal).comp hshift
  have hbase : Continuous (fun w : Mom d => 1 + ‖k + w‖ ^ 2) := by fun_prop
  have hInv : Measurable (fun w : Mom d =>
      ENNReal.ofReal (((1 + ‖k + w‖ ^ 2) ^ (s / 2))⁻¹)) :=
    (hbase.rpow_const (fun _ => Or.inl (by positivity))).measurable.inv.ennreal_ofReal
  have hR : Measurable R := hInv.mul hH
  have hprod (w : Mom d) : (L * R) w = ENNReal.ofReal |f (k + w)| * H w := by
    have hc := ofReal_weighted_abs_cancel ((1 + ‖k + w‖ ^ 2) ^ (s / 2)) (f (k + w)) 1
      (Real.rpow_pos_of_pos (by positivity) _)
    simp only [ENNReal.ofReal_one, mul_one, one_mul] at hc
    change ENNReal.ofReal |weightedFunction s f (k + w)| *
      (ENNReal.ofReal (((1 + ‖k + w‖ ^ 2) ^ (s / 2))⁻¹) * H w) = _
    rw [← mul_assoc]
    exact congrArg (fun a : ℝ≥0∞ => a * H w) hc
  have hLsq : (∫⁻ w : Mom d, L w ^ 2) = ENNReal.ofReal ((weightedL2Norm s f) ^ 2) := by
    calc
      _ = ∫⁻ w : Mom d, ENNReal.ofReal ((weightedFunction s f (k + w)) ^ 2) := by
        apply lintegral_congr
        intro w
        change ENNReal.ofReal |weightedFunction s f (k + w)| ^ 2 = _
        rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
      _ = ∫⁻ x : Mom d, ENNReal.ofReal ((weightedFunction s f x) ^ 2) :=
        lintegral_add_left_eq_self (fun x : Mom d => ENNReal.ofReal ((weightedFunction s f x) ^ 2)) k
      _ = _ := (ofReal_weightedL2Norm_sq s f hLf).symm
  have hRsq : (∫⁻ w : Mom d, R w ^ 2) =
      ∫⁻ w : Mom d, ENNReal.ofReal (japaneseDecay (2 * s) (k + w)) * (H w) ^ 2 := by
    apply lintegral_congr
    intro w
    change (ENNReal.ofReal (((1 + ‖k + w‖ ^ 2) ^ (s / 2))⁻¹) * H w) ^ 2 = _
    rw [mul_pow, ← ENNReal.ofReal_pow (by positivity) 2, inverse_weight_sq]
  have hconj : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hc := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hL.aemeasurable hR.aemeasurable
  simp only [ENNReal.rpow_two] at hc
  simp_rw [hprod] at hc
  rw [hLsq, hRsq, ennreal_ofReal_sq_half _ (weightedL2Norm_nonneg _ _)] at hc
  exact hc

end WaveTurbulence.WKEL2
