/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.FourierFirstMoment
public import WaveTurbulence.Foundations.Incoh.HalfLinkCellFourier

/-! # Fixed first-moment cost of the smooth half-width link profile -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp
open scoped ENNReal ContDiff FourierTransform

/-- One fixed dimensional constant pays a complete link frequency moment. -/
@[expose] def halfLinkFirstMomentConstant (d : ℕ) : ℝ :=
  1 + firstMomentFourierConstant (Mom d) (d+2) *
    Fourier.derivativeL1Sum (d+2) (halfLinkCell (0 : Fin d → ℤ))

theorem halfLinkFirstMomentConstant_pos (d : ℕ) : 0 < halfLinkFirstMomentConstant d := by
  have hC : 0 ≤ firstMomentFourierConstant (Mom d) (d+2) := by
    unfold firstMomentFourierConstant
    positivity
  have hD := Fourier.derivativeL1Sum_nonneg (d+2) (halfLinkCell (0 : Fin d → ℤ))
  unfold halfLinkFirstMomentConstant
  positivity

/-- The actual first moment is finite uniformly in every translating center. -/
theorem halfLinkCell_firstMoment_lintegral_le {d : ℕ} (c : Fin d → ℤ) :
    (∫⁻ ξ : Fin d → ℝ, ENNReal.ofReal (1+‖toLp 2 ξ‖) *
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => halfLinkCell c (toLp 2 y)) ξ‖ₑ) ≤
        ENNReal.ofReal (halfLinkFirstMomentConstant d) := by
  have hc := contDiff_halfLinkCell (0 : Fin d → ℤ)
  have hs : ContDiff ℝ ((d+2 : ℕ) : ℕ∞ω) (fun x : Mom d => halfLinkCell (0 : Fin d → ℤ) (toLp 2 (ofLp x))) := by
    simpa only [toLp_ofLp] using hc.of_le (show ((d+2 : ℕ) : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hi (j : ℕ) (_hj : j ≤ d+2) : Integrable (iteratedFDeriv ℝ j
      (fun x : Mom d => halfLinkCell (0 : Fin d → ℤ) (toLp 2 (ofLp x)))) := by
    simpa only [toLp_ofLp] using
      (hc.continuous_iteratedFDeriv (m := j) (by simp)).integrable_of_hasCompactSupport
        ((hasCompactSupport_halfLinkCell (0 : Fin d → ℤ)).iteratedFDeriv j)
  obtain ⟨hInt,hBound⟩ := coordinate_fourier_firstMoment_integrable_and_bound
    (f := fun y : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 y))
    (by omega : d+1 < d+2) hs hi
  have hh := ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ (fun ξ => by positivity))
  have he (ξ : Fin d → ℝ) : ENNReal.ofReal (1+‖toLp 2 ξ‖) *
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 y)) ξ‖ₑ =
      ENNReal.ofReal ((1+‖toLp 2 ξ‖) *
        ‖Fourier.timeFourier (fun y : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 y)) ξ‖) := by
    rw [← ofReal_norm,ENNReal.ofReal_mul (by positivity)]
  simp_rw [enorm_timeFourier_halfLinkCell_eq c,he]
  rw [← hh]
  apply ENNReal.ofReal_le_ofReal
  have hb : (∫ ξ : Fin d → ℝ, (1+‖toLp 2 ξ‖) *
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 y)) ξ‖) ≤
      firstMomentFourierConstant (Mom d) (d+2) *
        Fourier.derivativeL1Sum (d+2) (halfLinkCell (0 : Fin d → ℤ)) := by
    simpa only [toLp_ofLp] using hBound
  exact hb.trans (by unfold halfLinkFirstMomentConstant; linarith)

/-- The same fixed moment on the actual Euclidean momentum measure. -/
theorem halfLinkCell_euclidean_firstMoment_lintegral_le {d : ℕ} (c : Fin d → ℤ) :
    (∫⁻ ξ : Mom d, ENNReal.ofReal (1+‖ξ‖) * ‖𝓕 (halfLinkCell c) ξ‖ₑ) ≤
      ENNReal.ofReal (halfLinkFirstMomentConstant d) := by
  have hh := halfLinkCell_firstMoment_lintegral_le c
  rw [← (PiLp.volume_preserving_ofLp (Fin d)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
    (fun ξ : Fin d → ℝ => ENNReal.ofReal (1+‖toLp 2 ξ‖) *
      ‖Fourier.timeFourier (fun y : Fin d → ℝ => halfLinkCell c (toLp 2 y)) ξ‖ₑ)] at hh
  simpa only [Fourier.timeFourier_eq_euclidean,toLp_ofLp] using hh

end WaveTurbulence.RegAsymp
