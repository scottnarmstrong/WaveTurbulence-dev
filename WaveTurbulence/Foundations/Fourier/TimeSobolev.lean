/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeEuclidean
public import WaveTurbulence.Foundations.Fourier.FourierL1Sobolev
import Mathlib.Tactic

/-!
# Coordinate Fourier-L¹ norms and Sobolev bounds

The `d+1` derivative estimate for one momentum factor in TARGET L1007–L1012,
transported to the coordinate Fourier convention used by `timeFourier`.
-/

public section

open MeasureTheory WithLp
open scoped FourierTransform ENNReal

namespace WaveTurbulence.Fourier

/-- The dimension-dependent constant in the one-factor Fourier-L¹ bound. -/
@[expose] noncomputable def coordinateFourierL1Constant (d : ℕ) : ℝ :=
  fourierL1Constant (EuclideanSpace ℝ (Fin d)) (d + 1)

/-- Operator-norm `W^{d+1,1}` expression in Euclidean coordinates. -/
@[expose] noncomputable def coordinateSobolevL1 {d : ℕ} (f : (Fin d → ℝ) → ℂ) : ℝ :=
  derivativeL1Sum (d + 1) (fun x : EuclideanSpace ℝ (Fin d) => f (ofLp x))

/-- The one-factor estimate with a constant depending only on the dimension. -/
theorem timeFourierNorm_zero_le_sobolev {d : ℕ} {f : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ (d + 1) (fun x : EuclideanSpace ℝ (Fin d) => f (ofLp x)))
    (hi : ∀ j ≤ d + 1, Integrable
      (iteratedFDeriv ℝ j (fun x : EuclideanSpace ℝ (Fin d) => f (ofLp x)))) :
    timeFourierNorm 0 f ≤ ENNReal.ofReal (coordinateFourierL1Constant d) *
      ENNReal.ofReal (coordinateSobolevL1 f) := by
  have hbound := fourier_integrable_and_integral_norm_le
    (show Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < d + 1 by simp) hf hi
  have hfi : Integrable (fun x : EuclideanSpace ℝ (Fin d) => f (ofLp x)) := by
    apply (integrable_norm_iff hf.continuous.aestronglyMeasurable).mp
    simpa only [norm_iteratedFDeriv_zero] using (hi 0 (Nat.zero_le _)).norm
  have hp := PiLp.volume_preserving_ofLp (Fin d)
  have hfp : Integrable f := (hp.integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding).mp hfi
  rw [timeFourierNorm_eq_lintegral hfp]
  simp only [timeWeight, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  rw [← hp.lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
      (fun ξ => ‖timeFourier f ξ‖ₑ)]
  simp_rw [timeFourier_eq_euclidean, toLp_ofLp]
  unfold coordinateFourierL1Constant coordinateSobolevL1
  rw [← ofReal_integral_norm_eq_lintegral_enorm hbound.1,
    ← ENNReal.ofReal_mul (fourierL1Constant_nonneg (V := EuclideanSpace ℝ (Fin d)) (d + 1))]
  exact ENNReal.ofReal_le_ofReal hbound.2

end WaveTurbulence.Fourier
