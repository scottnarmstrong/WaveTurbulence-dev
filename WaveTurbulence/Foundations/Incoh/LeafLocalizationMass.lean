/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafCellFourierDecay

/-!
# Quantitative mass of the full smooth leaf localization

The one-factor coefficient is explicit and independent of the number of
leaves. Its finite products therefore give the required exponential bound.
-/

public section
noncomputable section
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- All literal cell-center coefficients are nonnegative. -/
theorem cellCenterWeight_nonneg {d : ℕ} (M : ℕ) (c : Fin d → ℤ) : 0 ≤ cellCenterWeight M c :=
  div_nonneg zero_le_one (pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) M)

/-- The explicit cell derivative-integral constant is nonnegative. -/
theorem leafCellSobolevConstant_nonneg (d N M : ℕ) : 0 ≤ leafCellSobolevConstant d N M := by
  unfold leafCellSobolevConstant
  exact mul_nonneg (by positivity) (Fourier.derivativeL1Sum_nonneg _ _)

/-- The actual Fourier constant is nonnegative. -/
theorem leafCellFourierConstant_nonneg (d M : ℕ) : 0 ≤ leafCellFourierConstant d M :=
  mul_nonneg (Fourier.fourierL1Constant_nonneg (V := Mom d) (d + 1))
    (leafCellSobolevConstant_nonneg d (d + 1) M)

/-- One-factor coefficient for summing every smooth leaf cell. -/
@[expose] def leafLocalizationConstant (d M : ℕ) : ℝ :=
  leafCellFourierConstant d M * ∑' c : Fin d → ℤ, cellCenterWeight M c

/-- The complete localization coefficient is controlled linearly by the source input norm. -/
theorem tsum_timeFourierNorm_leafCell_le {d K M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) :
    (∑' c : Fin d → ℤ,
      Fourier.timeFourierNorm 0 (fun x : Fin d → ℝ => leafCell f c (WithLp.toLp 2 x))) ≤
        ENNReal.ofReal (leafLocalizationConstant d M * B) := by
  have hC : 0 ≤ leafCellFourierConstant d M * B :=
    mul_nonneg (leafCellFourierConstant_nonneg d M) hB
  calc
    _ ≤ ∑' c : Fin d → ℤ,
        ENNReal.ofReal (leafCellFourierConstant d M * B * cellCenterWeight M c) :=
      ENNReal.tsum_le_tsum (fun c => timeFourierNorm_leafCell_le hK hB h c)
    _ = ENNReal.ofReal (leafCellFourierConstant d M * B) *
        ENNReal.ofReal (∑' c : Fin d → ℤ, cellCenterWeight M c) := by
      simp_rw [ENNReal.ofReal_mul hC]
      rw [ENNReal.tsum_mul_left,
        ← ENNReal.ofReal_tsum_of_nonneg (cellCenterWeight_nonneg M) (summable_cellCenterWeight hM)]
    _ = _ := by
      rw [← ENNReal.ofReal_mul hC]
      congr 1
      unfold leafLocalizationConstant
      ring

end WaveTurbulence.Incoh
