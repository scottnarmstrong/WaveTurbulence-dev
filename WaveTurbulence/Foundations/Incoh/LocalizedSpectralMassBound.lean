/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedSpectralMass
public import WaveTurbulence.Foundations.Incoh.LeafArrayLocalization

/-!
# Summable coefficient of all actual leaf localizations

The spectral mass has a dimensional exponential link cost and a summable
leaf-array coefficient, before any analytic oscillatory estimate is applied.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Fixed dimensional Fourier-L¹ constant for the half-width link profile. -/
@[expose] def halfCellFourierConstant (d : ℕ) : ℝ :=
  1 + (Fourier.timeFourierNorm 0
    (fun y : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 y))).toReal

theorem halfCellFourierConstant_pos (d : ℕ) : 0 < halfCellFourierConstant d := by
  unfold halfCellFourierConstant
  positivity

theorem timeFourierNorm_halfLinkCell_le (d : ℕ) (c : Fin d → ℤ) :
    Fourier.timeFourierNorm 0 (fun y : Fin d → ℝ => halfLinkCell c (toLp 2 y)) ≤
      ENNReal.ofReal (halfCellFourierConstant d) := by
  rw [timeFourierNorm_halfLinkCell_eq]
  have ht := (timeFourierNorm_halfLinkCell_lt_top 0 (0 : Fin d → ℤ)).ne
  calc
    _ = ENNReal.ofReal (Fourier.timeFourierNorm 0
        (fun y : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 y))).toReal :=
      (ENNReal.ofReal_toReal ht).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by unfold halfCellFourierConstant; linarith)

/-- Actual reference mass bound for one leaf-cell array. -/
theorem lintegral_enorm_localizedSpectralReference_le {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      ‖localizedSpectralReference (n := n) f c ξ‖ₑ) ≤
      (∏ a, Fourier.timeFourierNorm 0 (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y))) *
        ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n) := by
  rw [lintegral_enorm_localizedSpectralReference f c hK hB h, Fintype.prod_sum_type]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∏ _p : Fin n × Fin 2, ENNReal.ofReal (halfCellFourierConstant d) :=
      Finset.prod_le_prod (fun _ _ => timeFourierNorm_halfLinkCell_le d 0)
    _ = _ := by simp [Nat.mul_comm]

/-- The full countable leaf-array coefficient is finite with an explicit exponential bound. -/
theorem tsum_lintegral_enorm_localizedSpectralReference_le {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) {B : ℝ}
    (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∑' c : Fin m → Fin d → ℤ,
      ∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        ‖localizedSpectralReference (n := n) f c ξ‖ₑ) ≤
      ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
        ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n) := by
  calc
    _ ≤ ∑' c : Fin m → Fin d → ℤ,
        (∏ a, Fourier.timeFourierNorm 0 (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y))) *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n) :=
      ENNReal.tsum_le_tsum (fun c => lintegral_enorm_localizedSpectralReference_le f c hK hB h)
    _ = _ := by rw [ENNReal.tsum_mul_right]
    _ ≤ _ := mul_le_mul' (tsum_prod_timeFourierNorm_leafCell_le f hK hM hB h) le_rfl

end WaveTurbulence.Incoh
