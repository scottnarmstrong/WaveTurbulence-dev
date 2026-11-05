/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafFirstMoment
public import WaveTurbulence.Foundations.RegAsymp.FrequencyProductMoment
public import WaveTurbulence.Foundations.Incoh.LeafArrayLocalization

/-! # Summing all leaf centers with one full frequency moment -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp
open scoped ENNReal

/-- The fixed-dimensional coefficient paying the moment and every center. -/
@[expose] def leafFirstMomentConstant (d M : ℕ) : ℝ :=
  firstMomentFourierConstant (Mom d) (d+2) * leafCellSobolevConstant d (d+2) M *
    ∑' c : Fin d → ℤ, cellCenterWeight M c

/-- The actual Fourier first moments, summed over every leaf center. -/
theorem tsum_leafCell_firstMoment_le {d K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B) :
    (∑' c : Fin d → ℤ, ∫⁻ ξ : Fin d → ℝ, ENNReal.ofReal (1+‖toLp 2 ξ‖) *
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F c (toLp 2 y)) ξ‖ₑ) ≤
        ENNReal.ofReal (leafFirstMomentConstant d M * B) := by
  let C := firstMomentFourierConstant (Mom d) (d+2) * leafCellSobolevConstant d (d+2) M
  have hC : 0 ≤ C * B := by
    have h1 : 0 ≤ firstMomentFourierConstant (Mom d) (d+2) := by
      unfold firstMomentFourierConstant
      positivity
    exact mul_nonneg (mul_nonneg h1 (leafCellSobolevConstant_nonneg _ _ _)) hB
  calc
    _ ≤ ∑' c : Fin d → ℤ, ENNReal.ofReal (C * B * cellCenterWeight M c) :=
      ENNReal.tsum_le_tsum (fun c => leafCell_coordinate_firstMoment_lintegral_le hK hB hF c)
    _ = ENNReal.ofReal (C * B) * ENNReal.ofReal (∑' c : Fin d → ℤ, cellCenterWeight M c) := by
      simp_rw [ENNReal.ofReal_mul hC]
      rw [ENNReal.tsum_mul_left,
        ← ENNReal.ofReal_tsum_of_nonneg (cellCenterWeight_nonneg M) (summable_cellCenterWeight hM)]
    _ = _ := by
      rw [← ENNReal.ofReal_mul hC]
      congr 1
      unfold C leafFirstMomentConstant
      ring

/-- The complete actual density pays only a geometric cost in the number
of leaves, after summing every localization center and the sum-frequency moment. -/
theorem tsum_leafFrequency_firstMoment_le {d m K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B) :
    (∑' c : Fin m → Fin d → ℤ,
      ∫⁻ α : Fin m → Fin d → ℝ, ENNReal.ofReal (1+∑ a, ‖toLp 2 (α a)‖) *
        ∏ a, ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F (c a) (toLp 2 y)) (α a)‖ₑ) ≤
      ENNReal.ofReal (leafFirstMomentConstant d M * B) ^ m := by
  have hmeas (c : Fin d → ℤ) : Measurable (fun ξ : Fin d → ℝ =>
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F c (toLp 2 y)) ξ‖ₑ) := by
    have hnorm := timeFourierNorm_leafCell_le (by omega : d+1 ≤ K) hB hF c
    have hi := Fourier.integrable_of_timeFourierNorm_lt_top (lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top)
    exact (Fourier.timeFourier_continuous hi).measurable.enorm
  calc
    _ ≤ ∑' c : Fin m → Fin d → ℤ, ∏ a, ∫⁻ ξ : Fin d → ℝ,
        ENNReal.ofReal (1+‖toLp 2 ξ‖) *
          ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F (c a) (toLp 2 y)) ξ‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro c
      exact lintegral_sum_frequency_moment_le (fun ξ : Fin d → ℝ => ‖toLp 2 ξ‖)
        (PiLp.continuous_toLp 2 _).norm.measurable (fun _ => norm_nonneg _)
        _ (fun a => hmeas (c a))
    _ = ∏ a : Fin m, ∑' c : Fin d → ℤ, ∫⁻ ξ : Fin d → ℝ,
        ENNReal.ofReal (1+‖toLp 2 ξ‖) *
          ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F c (toLp 2 y)) ξ‖ₑ :=
      tsum_fin_product_ennreal m (fun (_a : Fin m) (c : Fin d → ℤ) =>
        ∫⁻ ξ : Fin d → ℝ, ENNReal.ofReal (1+‖toLp 2 ξ‖) *
          ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F c (toLp 2 y)) ξ‖ₑ)
    _ ≤ ∏ _a : Fin m, ENNReal.ofReal (leafFirstMomentConstant d M * B) :=
      Finset.prod_le_prod (fun _ _ => tsum_leafCell_firstMoment_le hK hM hB hF)
    _ = _ := by simp

end WaveTurbulence.RegAsymp
