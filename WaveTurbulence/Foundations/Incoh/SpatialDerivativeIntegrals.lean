/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialInputBounds
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import WaveTurbulence.Foundations.Fourier.FourierL1Sobolev

/-!
# Integrable derivatives from the literal source spatial norm

The source Japanese-bracket decay supplies the actual integrable majorant.
All constants depend only on dimension and the fixed derivative/decay orders.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- The actual source spatial decay profile. -/
@[expose] def spatialDecay {d : ℕ} (M : ℕ) (x : Mom d) : ℝ :=
  1 / Fourier.momentumBracket x ^ M

/-- The source profile is exactly the standard integrable radial power. -/
theorem spatialDecay_eq_rpow {d : ℕ} (M : ℕ) (x : Mom d) :
    spatialDecay M x = (1 + ‖x‖ ^ 2) ^ (-(M : ℝ) / 2) := by
  rw [spatialDecay, Fourier.momentumBracket, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div,
    ← Real.rpow_neg (by positivity)]
  congr 1
  ring

/-- Decay faster than the momentum dimension is integrable. -/
theorem integrable_spatialDecay {d M : ℕ} (hM : d < M) :
    Integrable (spatialDecay (d := d) M) := by
  have hr : (Module.finrank ℝ (Mom d) : ℝ) < (M : ℝ) := by
    simpa using (show (d : ℝ) < (M : ℝ) by exact_mod_cast hM)
  rw [show spatialDecay (d := d) M = (fun x : Mom d => (1 + ‖x‖ ^ 2) ^ (-(M : ℝ) / 2)) from
    funext (spatialDecay_eq_rpow M)]
  exact integrable_rpow_neg_one_add_norm_sq hr

/-- Actual Fréchet derivatives are integrable under the source's weighted coordinate norm bound. -/
theorem integrable_iteratedFDeriv_of_spatialNorm {d K M j : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : 0 < K) (hM : d < M) (hB : 0 ≤ B)
    (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) (hj : j ≤ K) :
    Integrable (iteratedFDeriv ℝ j f) := by
  have hc := contDiff_of_spatialNorm_le hK h
  apply ((integrable_spatialDecay hM).const_mul ((d : ℝ) ^ j * B)).mono'
    (hc.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    have hb := norm_iteratedFDeriv_le_of_spatialNorm hB h hj x
    simpa only [spatialDecay, div_eq_mul_inv, one_mul, mul_assoc] using hb)

/-- The actual `L¹` norm of each operator derivative is controlled by the source input. -/
theorem integral_norm_iteratedFDeriv_le_of_spatialNorm {d K M j : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : 0 < K) (hM : d < M) (hB : 0 ≤ B)
    (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) (hj : j ≤ K) :
    (∫ x, ‖iteratedFDeriv ℝ j f x‖) ≤ ((d : ℝ) ^ j * B) * ∫ x : Mom d, spatialDecay M x := by
  rw [← integral_const_mul]
  apply integral_mono (integrable_iteratedFDeriv_of_spatialNorm hK hM hB h hj).norm
    ((integrable_spatialDecay hM).const_mul _)
  intro x
  simpa only [spatialDecay, div_eq_mul_inv, one_mul, mul_assoc] using
    norm_iteratedFDeriv_le_of_spatialNorm hB h hj x

/-- A concrete dimension/order constant for the one-factor derivative integral sum. -/
@[expose] def sourceSobolevConstant (d N M : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (N + 1), (d : ℝ) ^ j) * ∫ x : Mom d, spatialDecay M x

/-- The source spatial norm controls the full derivative `L¹` sum used by Fourier inversion. -/
theorem derivativeL1Sum_le_of_spatialNorm {d K M N : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : 0 < K) (hM : d < M) (hB : 0 ≤ B)
    (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) (hN : N ≤ K) :
    Fourier.derivativeL1Sum N f ≤ sourceSobolevConstant d N M * B := by
  unfold Fourier.derivativeL1Sum
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1), ((d : ℝ) ^ j * B) * ∫ x : Mom d, spatialDecay M x := by
      apply Finset.sum_le_sum
      intro j hj
      exact integral_norm_iteratedFDeriv_le_of_spatialNorm hK hM hB h
        ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hN)
    _ = _ := by
      simp only [sourceSobolevConstant, ← Finset.sum_mul]
      ring

end WaveTurbulence.Incoh
