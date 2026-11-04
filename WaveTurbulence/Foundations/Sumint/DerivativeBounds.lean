/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.WeightBounds
public import WaveTurbulence.Foundations.Sumint.MultilinearBounds
public import WaveTurbulence.Foundations.Sumint.MultiIndices
import Mathlib.Tactic

/-!
# Finite Fréchet derivative bounds from the exact S norm

The coordinate-word bridge is recompiled against the local snapshot-5
System. No smoothness beyond the positive order already in the draft norm
is assumed.
-/

public section

open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- Every Fréchet derivative up to the positive draft norm order has the same spatial decay. -/
theorem norm_iteratedFDeriv_le_of_SNorm_le {d N K n : ℕ} (hN : N ≠ 0) (hn : n ≤ N)
    {F : Mom d → ℂ} {B : ℝ} (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B)
    (x : Mom d) :
    ‖iteratedFDeriv ℝ n F x‖ ≤ (d : ℝ) ^ n * (B / jbr x ^ K) := by
  have hf := contDiff_of_SNorm_le hN hF
  have hfn : ContDiff ℝ n F := hf.of_le (by exact_mod_cast hn)
  have hp : 0 < jbr x ^ K := pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_jbr x)) _
  apply multilinear_norm_le_of_coordinate_bounds _ (div_nonneg hB hp.le)
  intro ρ
  change ‖Fourier.momentumDerivative ρ F x‖ ≤ B / jbr x ^ K
  rw [NormBridgeScratch.momentumDerivative_eq_iterPartial_counts ρ hfn]
  have hρ : ∑ j, (List.ofFn ρ).count j ≤ N := by
    rw [NormBridgeScratch.sum_counts, List.length_ofFn]
    exact hn
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_comm] using weighted_multiindex_norm_le_of_SNorm_le hB hF _ hρ x

end WaveTurbulence.Sumint
