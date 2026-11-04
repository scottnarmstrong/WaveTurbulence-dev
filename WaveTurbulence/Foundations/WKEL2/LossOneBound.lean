/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.LossOneSquared
public import WaveTurbulence.Foundations.WKEL2.SpatialCauchyENN

/-!
# Uniform absolute first-loss bound

Research-note Proposition 6. Resonant measure omits the delta factor one half.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Uniform first-loss bound for absolute Borel weighted-L² inputs. -/
theorem exists_uniform_lossOne_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ g h : Mom d → ℝ,
      Measurable g → Measurable h → MemLp (weightedFunction s g) 2 →
      MemLp (weightedFunction s h) 2 → ∀ k : Mom d,
      (∫⁻ p, ENNReal.ofReal |g (k + p.1 + p.2)| * ENNReal.ofReal |h (k + p.2)|
        ∂resonantMeasure e) ≤
        ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s g * weightedL2Norm s h) := by
  obtain ⟨C, hC, hb⟩ := exists_sphericalLossAverage_square_bound hd s hs
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun e he g h hg hh hLg hLh k => ?_⟩
  have hroot : (ENNReal.ofReal C) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt C) := by
    calc
      _ = (ENNReal.ofReal ((Real.sqrt C) ^ 2)) ^ ((1 : ℝ) / 2) := by rw [Real.sq_sqrt hC]
      _ = _ := ennreal_ofReal_sq_half _ (Real.sqrt_nonneg _)
  rw [lintegral_lossOne_spherical he (by omega) hg hh k]
  calc
    _ ≤ ENNReal.ofReal (weightedL2Norm s g) *
        (∫⁻ w : Mom d, ENNReal.ofReal (japaneseDecay (2 * s) (k + w)) *
          (sphericalLossAverage h k w) ^ 2) ^ ((1 : ℝ) / 2) :=
      lintegral_weighted_spatial_cauchy s hg hLg (measurable_sphericalLossAverage hh k) k
    _ ≤ ENNReal.ofReal (weightedL2Norm s g) *
        (ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s h) ^ 2)) ^ ((1 : ℝ) / 2) :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hb h hh hLh k) (by norm_num))
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hroot,
        ennreal_ofReal_sq_half _ (weightedL2Norm_nonneg _ _),
        ENNReal.ofReal_mul (weightedL2Norm_nonneg _ _)]
      ac_rfl

end WaveTurbulence.WKEL2
