/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.HalfLinkCellFourier
public import WaveTurbulence.Foundations.Incoh.LeafCellFourierDecay
public import WaveTurbulence.Foundations.Fourier.TimeProduct
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Fourier inversion of actual leaf and link cells

TARGET (incohproof6–8). Finite source smoothness supplies the leaf Fourier
integrability; fixed smooth compact profiles supply the link integrability.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Conditional inversion helper used with the actual, independently proved cell norms. -/
theorem eq_positiveFourierIntegral_of_norm_lt_top {d : ℕ} {f : (Fin d → ℝ) → ℂ}
    (hc : Continuous f) (hf : Fourier.timeFourierNorm 0 f < ⊤) (x : Fin d → ℝ) :
    f x = ∫ ξ : Fin d → ℝ, Real.fourierChar (Fourier.timePairing d ξ x) •
      Fourier.timeFourier f ξ := by
  have hi := Fourier.integrable_of_timeFourierNorm_lt_top hf
  have hfi := Fourier.integrable_timeFourier_of_norm_lt_top (le_refl (0 : ℝ)) hf
  calc
    _ = Fourier.timeFourier (Fourier.timeFourier f) (-x) :=
      (Fourier.timeFourier_inversion hi hfi hc x).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ξ => by simp only [Fourier.timeFourier, map_neg, neg_neg])

/-- The actual localized source leaf is recovered pointwise from its Fourier density. -/
theorem leafCell_eq_fourierIntegral {d K M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : d + 1 ≤ K) (hB : 0 ≤ B) (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B)
    (c : Fin d → ℤ) (x : Mom d) :
    leafCell f c x = ∫ ξ : Fin d → ℝ,
      Real.fourierChar (Fourier.timePairing d ξ (ofLp x)) •
        Fourier.timeFourier (fun y : Fin d → ℝ => leafCell f c (toLp 2 y)) ξ := by
  have hc := (contDiff_leafCell (contDiff_of_spatialNorm_le
    ((Nat.zero_lt_succ d).trans_le hK) h) c).continuous.comp (PiLp.continuous_toLp 2 _)
  have hf := lt_of_le_of_lt (timeFourierNorm_leafCell_le hK hB h c)
    (ENNReal.ofReal_lt_top : ENNReal.ofReal (leafCellFourierConstant d M * B * cellCenterWeight M c) < ⊤)
  simpa only [Function.comp_def, toLp_ofLp] using eq_positiveFourierIntegral_of_norm_lt_top hc hf (ofLp x)

/-- The actual half-width link cell is recovered from its actual Fourier density. -/
theorem halfLinkCell_eq_fourierIntegral {d : ℕ} (c : Fin d → ℤ) (x : Mom d) :
    halfLinkCell c x = ∫ ξ : Fin d → ℝ,
      Real.fourierChar (Fourier.timePairing d ξ (ofLp x)) •
        Fourier.timeFourier (fun y : Fin d → ℝ => halfLinkCell c (toLp 2 y)) ξ := by
  have hc := (contDiff_halfLinkCell c).continuous.comp (PiLp.continuous_toLp 2 _)
  simpa only [Function.comp_def, toLp_ofLp] using eq_positiveFourierIntegral_of_norm_lt_top hc
    (timeFourierNorm_halfLinkCell_lt_top 0 c) (ofLp x)

end WaveTurbulence.Incoh
