/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralMomentMass

/-! # Countably summable actual spectral derivative moments -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The explicit individual leaf moment constant is nonnegative. -/
theorem leafCellFourierMomentConstant_nonneg (d J M : ℕ) : 0 ≤ leafCellFourierMomentConstant d J M := by
  unfold leafCellFourierMomentConstant
  apply mul_nonneg _ (leafCellSobolevConstant_nonneg _ _ _)
  unfold weightedFourierL1Constant
  exact mul_nonneg (by positivity) (integral_nonneg (fun ξ => Real.rpow_nonneg (by positivity) _))

/-- Complete dimensional coefficient of all leaf-center localizations with a Fourier moment. -/
@[expose] def leafMomentLocalizationConstant (d J M : ℕ) : ℝ :=
  leafCellFourierMomentConstant d J M * ∑' c : Fin d → ℤ, cellCenterWeight M c

/-- Exact positive center-series summation used for the moment envelope. -/
theorem tsum_ofReal_div_momentumBracket_intVec {d M : ℕ} (hM : 2 * d ≤ M) {A : ℝ} (hA : 0 ≤ A) :
    (∑' c : Fin d → ℤ, ENNReal.ofReal (A / Fourier.momentumBracket (NTSP.intVec c) ^ M)) =
      ENNReal.ofReal (A * ∑' c : Fin d → ℤ, cellCenterWeight M c) := by
  have he (c : Fin d → ℤ) : A / Fourier.momentumBracket (NTSP.intVec c) ^ M = A * cellCenterWeight M c := by
    simp only [cellCenterWeight, div_eq_mul_inv, one_mul]
  simp_rw [he, ENNReal.ofReal_mul hA]
  rw [ENNReal.tsum_mul_left,
    ← ENNReal.ofReal_tsum_of_nonneg (cellCenterWeight_nonneg M) (summable_cellCenterWeight hM),
    ← ENNReal.ofReal_mul hA]

end WaveTurbulence.Incoh
