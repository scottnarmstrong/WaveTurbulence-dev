/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialInputBounds

/-! # Scalar multiplication in the landed finite spatial norms -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp

/-- Multiplying a finite spatial input by a scalar scales its literal
coordinate-word norm by at most the norm of that scalar. -/
theorem spatialNorm_const_mul_le {d N M : ℕ} (hN : 0 < N) {f : Mom d → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hF : Fourier.spatialNorm N M f ≤ ENNReal.ofReal B) (c : ℂ) :
    Fourier.spatialNorm N M (fun x => c*f x) ≤ ENNReal.ofReal (‖c‖*B) := by
  have hf := Incoh.contDiff_of_spatialNorm_le hN hF
  have hc : ContDiff ℝ N (fun x => c*f x) := hf.const_smul c
  rw [Fourier.spatialNorm,ite_eq_left (Or.inr hc)]
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  apply iSup_le
  intro ρ
  unfold Fourier.momentumSupNorm
  apply iSup_le
  intro k
  have he : Fourier.momentumDerivative ρ (fun x => c*f x) k =
      c*Fourier.momentumDerivative ρ f k := by
    unfold Fourier.momentumDerivative
    have hdj : ContDiffAt ℝ j f k := (hf.of_le (by exact_mod_cast hj)).contDiffAt
    rw [show iteratedFDeriv ℝ j (fun x => c*f x) k =
      c • iteratedFDeriv ℝ j f k from iteratedFDeriv_const_smul_apply' (a := c) hdj]
    rfl
  rw [he,← ofReal_norm,norm_mul]
  have hw : 0 ≤ Fourier.momentumBracket k ^ M :=
    pow_nonneg (Real.sqrt_nonneg _) _
  rw [← ENNReal.ofReal_mul hw]
  apply ENNReal.ofReal_le_ofReal
  calc
    Fourier.momentumBracket k^M*(‖c‖*‖Fourier.momentumDerivative ρ f k‖) =
        ‖c‖*(Fourier.momentumBracket k^M*‖Fourier.momentumDerivative ρ f k‖) := by ring
    _ ≤ ‖c‖*B := mul_le_mul_of_nonneg_left
      (Incoh.weighted_momentumDerivative_le_of_spatialNorm hB hF hj ρ k) (norm_nonneg _)

end WaveTurbulence.RegAsymp
