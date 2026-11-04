/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafCellProfile
public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay
public import WaveTurbulence.Foundations.Incoh.LocalizedSobolevMultiplication

/-!
# Summable center decay of the actual localized derivative integrals

The source weighted spatial norm, the actual cell support and the landed
product estimates give a uniform coefficient for each smooth momentum cell.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Explicit one-cell constant, independent of every localization center and input function. -/
@[expose] def leafCellSobolevConstant (d N M : ℕ) : ℝ :=
  ((N : ℝ) + 1) * (2 : ℝ) ^ N * (max 1 (d : ℝ)) ^ N * (2 + Real.sqrt d) ^ M *
    Fourier.derivativeL1Sum N (leafCellProfile d 0)

/-- TARGET Step (2): the literal smooth cell has rapid decay in its center. -/
theorem derivativeL1Sum_leafCell_le {d K N M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : 0 < K) (hN : N ≤ K) (hB : 0 ≤ B)
    (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) (c : Fin d → ℤ) :
    Fourier.derivativeL1Sum N (leafCell f c) ≤
      leafCellSobolevConstant d N M * B / Fourier.momentumBracket (NTSP.intVec c) ^ M := by
  let D := (max 1 (d : ℝ)) ^ N *
    (B * (2 + Real.sqrt d) ^ M / Fourier.momentumBracket (NTSP.intVec c) ^ M)
  have hbr : 0 < Fourier.momentumBracket (NTSP.intVec c) ^ M :=
    pow_pos (lt_of_lt_of_le zero_lt_one (one_le_momentumBracket _)) M
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hf := (contDiff_of_spatialNorm_le hK h).of_le (show (N : ℕ∞ω) ≤ K by exact_mod_cast hN)
  have hg := (contDiff_leafCellProfile d (NTSP.intVec c)).of_le (show (N : ℕ∞ω) ≤ ∞ by simp)
  have hb (j : ℕ) (hj : j ≤ N) (x : Mom d) (hx : x ∈ tsupport (leafCellProfile d (NTSP.intVec c))) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ D := by
    have hs := norm_iteratedFDeriv_le_center_decay hB (Real.sqrt_nonneg (d : ℝ)) h
      (hj.trans hN) (tsupport_leafCellProfile_subset d (NTSP.intVec c) hx)
    have hp : (d : ℝ) ^ j ≤ (max 1 (d : ℝ)) ^ N :=
      (pow_le_pow_left₀ (Nat.cast_nonneg d) (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) hj)
    exact hs.trans (mul_le_mul_of_nonneg_right hp (by positivity))
  have hprod := derivativeL1Sum_mul_le_on_support f (leafCellProfile d (NTSP.intVec c)) hf hg
    (hasCompactSupport_leafCellProfile d (NTSP.intVec c)) hD hb
  change Fourier.derivativeL1Sum N (fun x => f x * leafCellProfile d (NTSP.intVec c) x) ≤ _
  apply hprod.trans
  calc
    _ ≤ (((N : ℝ) + 1) * (2 : ℝ) ^ N * D) * Fourier.derivativeL1Sum N (leafCellProfile d 0) :=
      mul_le_mul_of_nonneg_left (derivativeL1Sum_leafCellProfile_le d N (NTSP.intVec c)) (by positivity)
    _ = _ := by simp only [leafCellSobolevConstant, D, div_eq_mul_inv]; ring

end WaveTurbulence.Incoh
