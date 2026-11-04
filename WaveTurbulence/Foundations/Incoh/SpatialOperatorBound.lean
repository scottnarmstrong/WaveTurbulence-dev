/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay

/-! # Bounding literal source spatial norms by actual operator derivatives -/

public section
noncomputable section
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- The literal coordinate-word spatial norm follows from bounds on actual operator derivatives. -/
theorem spatialNorm_le_of_weighted_operator_bound {d N M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hf : ContDiff ℝ N f)
    (hb : ∀ j ≤ N, ∀ k, Fourier.momentumBracket k ^ M * ‖iteratedFDeriv ℝ j f k‖ ≤ B) :
    Fourier.spatialNorm N M f ≤ ENNReal.ofReal B := by
  rw [Fourier.spatialNorm, ite_eq_left (Or.inr hf)]
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  apply iSup_le
  intro ρ
  unfold Fourier.momentumSupNorm
  apply iSup_le
  intro k
  have hw : 0 ≤ Fourier.momentumBracket k ^ M :=
    pow_nonneg (zero_le_one.trans (one_le_momentumBracket k)) M
  have hc : ‖Fourier.momentumDerivative ρ f k‖ ≤ ‖iteratedFDeriv ℝ j f k‖ := by
    simpa only [Fourier.momentumDerivative, EuclideanSpace.single, PiLp.norm_single,
      norm_one, Finset.prod_const_one, mul_one] using
      (iteratedFDeriv ℝ j f k).le_opNorm (fun i => EuclideanSpace.single (ρ i) 1)
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hw]
  exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hc hw).trans (hb j hj k))

end WaveTurbulence.Incoh
