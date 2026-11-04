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

/-- The full actual higher-moment localization mass has an explicit exponential bound. -/
theorem tsum_lintegral_enorm_localizedSpectralMomentReference_le {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d + 1 + J ≤ K)
    (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∑' c : Fin m → Fin d → ℤ,
      ∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ, ‖localizedSpectralMomentReference J f c ξ‖ₑ) ≤
        ENNReal.ofReal (leafMomentLocalizationConstant d J M * B) ^ m *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n) := by
  apply (ENNReal.tsum_le_tsum (fun c =>
    lintegral_enorm_localizedSpectralMomentReference_le J f c hK hB h)).trans_eq
  rw [ENNReal.tsum_mul_right, tsum_fin_product_ennreal m (fun (_ : Fin m) c =>
    ENNReal.ofReal (leafCellFourierMomentConstant d J M * B /
      Fourier.momentumBracket (NTSP.intVec c) ^ M))]
  simp_rw [tsum_ofReal_div_momentumBracket_intVec hM
    (mul_nonneg (leafCellFourierMomentConstant_nonneg d J M) hB)]
  congr 1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  unfold leafMomentLocalizationConstant
  ring

end WaveTurbulence.Incoh
