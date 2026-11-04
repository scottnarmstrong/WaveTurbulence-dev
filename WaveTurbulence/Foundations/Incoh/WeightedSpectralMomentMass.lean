/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralMomentSummability

/-! # Actual spectral moment envelopes after transferring the root weight to leaf centers -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The remaining center-decay coefficient after paying for the source root weight. -/
@[expose] def leafWeightedMomentLocalizationConstant (d J M W : ℕ) : ℝ :=
  leafCellFourierMomentConstant d J M * ∑' c : Fin d → ℤ, cellCenterWeight (M - W) c

/-- Paying the root weight at every source leaf center leaves exactly `M-W` powers of decay. -/
theorem weighted_lintegral_enorm_localizedSpectralMomentReference_le {d n m K M W : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hWM : W ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    ENNReal.ofReal (∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) ^ W) *
      (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ, ‖localizedSpectralMomentReference J f c ξ‖ₑ) ≤
        (∏ a : Fin m, ENNReal.ofReal (leafCellFourierMomentConstant d J M * B /
          Fourier.momentumBracket (NTSP.intVec (c a)) ^ (M - W))) *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n) := by
  apply (mul_le_mul' le_rfl (lintegral_enorm_localizedSpectralMomentReference_le J f c hK hB h)).trans_eq
  rw [← mul_assoc, ENNReal.ofReal_prod_of_nonneg (fun a _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W), ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [← ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W : 0 ≤ Fourier.momentumBracket (NTSP.intVec (c a)) ^ W)]
  congr 1
  have hp : 0 < Fourier.momentumBracket (NTSP.intVec (c a)) :=
    zero_lt_one.trans_le (one_le_momentumBracket _)
  have he : Fourier.momentumBracket (NTSP.intVec (c a)) ^ M =
      Fourier.momentumBracket (NTSP.intVec (c a)) ^ W *
        Fourier.momentumBracket (NTSP.intVec (c a)) ^ (M - W) := by
    rw [← pow_add]
    congr 1
    omega
  rw [he]
  field_simp

/-- The complete root-weighted actual spectral derivative envelope remains summable. -/
theorem tsum_weighted_lintegral_enorm_localizedSpectralMomentReference_le {d n m K M W : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d + 1 + J ≤ K)
    (hM : W + 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∑' c : Fin m → Fin d → ℤ,
      ENNReal.ofReal (∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) ^ W) *
        (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ, ‖localizedSpectralMomentReference J f c ξ‖ₑ)) ≤
      ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W * B) ^ m *
        ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n) := by
  apply (ENNReal.tsum_le_tsum (fun c =>
    weighted_lintegral_enorm_localizedSpectralMomentReference_le J f c hK (by omega) hB h)).trans_eq
  rw [ENNReal.tsum_mul_right, tsum_fin_product_ennreal m (fun (_ : Fin m) c =>
    ENNReal.ofReal (leafCellFourierMomentConstant d J M * B /
      Fourier.momentumBracket (NTSP.intVec c) ^ (M - W)))]
  simp_rw [tsum_ofReal_div_momentumBracket_intVec (by omega : 2 * d ≤ M - W)
    (mul_nonneg (leafCellFourierMomentConstant_nonneg d J M) hB)]
  congr 1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  unfold leafWeightedMomentLocalizationConstant
  ring

end WaveTurbulence.Incoh
