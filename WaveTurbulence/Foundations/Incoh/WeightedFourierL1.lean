/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourierL1Sobolev

/-! # Finite Sobolev bounds for polynomially weighted Fourier mass

TARGET Proposition 5.1 Step (1): momentum derivatives of the actual
spectral extension require only the available finite input derivatives.
-/

public section
noncomputable section
open MeasureTheory Module
open scoped FourierTransform ContDiff

namespace WaveTurbulence.Incoh

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Explicit finite Sobolev coefficient for a polynomial Fourier moment. -/
@[expose] def weightedFourierL1Constant (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (N J : ℕ) : ℝ :=
  (2 : ℝ) ^ (N + J - 1) * (1 + 2 ^ (N + J)) *
    ∫ ξ : V, (1 + ‖ξ‖) ^ (-(N : ℝ))

/-- A weighted Fourier moment consumes exactly its degree in addition to the dimension margin. -/
theorem integrable_weighted_fourier_and_integral_le {N J : ℕ} {f : V → ℂ}
    (hN : finrank ℝ V < N) (hf : ContDiff ℝ (N + J) f)
    (hi : ∀ j ≤ N + J, Integrable (iteratedFDeriv ℝ j f)) :
    Integrable (fun ξ => (1 + ‖ξ‖) ^ J * ‖𝓕 f ξ‖) ∧
      (∫ ξ, (1 + ‖ξ‖) ^ J * ‖𝓕 f ξ‖) ≤
        weightedFourierL1Constant V N J * Fourier.derivativeL1Sum (N + J) f := by
  have henv : Integrable (fun ξ : V => (1 + ‖ξ‖) ^ (-(N : ℝ))) :=
    integrable_one_add_norm (by exact_mod_cast hN)
  let C := (2 : ℝ) ^ (N + J - 1) * (1 + 2 ^ (N + J)) * Fourier.derivativeL1Sum (N + J) f
  have hbound (ξ : V) : (1 + ‖ξ‖) ^ J * ‖𝓕 f ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
    have hp : 0 < (1 + ‖ξ‖) ^ N := pow_pos (by positivity) _
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
    apply (le_div_iff₀ hp).mpr
    have h := Fourier.fourier_polynomial_weight_le hf hi ξ
    dsimp only [C]
    convert h using 1; ring
  have hfi : Integrable f := by
    have h : Integrable (fun x => ‖f x‖) := by
      simpa only [norm_iteratedFDeriv_zero] using (hi 0 (Nat.zero_le _)).norm
    exact (integrable_norm_iff hf.continuous.aestronglyMeasurable).mp h
  have hmeas : AEStronglyMeasurable (fun ξ : V => (1 + ‖ξ‖) ^ J * ‖𝓕 f ξ‖) := by
    apply Continuous.aestronglyMeasurable
    exact ((continuous_const.add continuous_norm).pow J).mul
      (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hfi).norm
  have hInt : Integrable (fun ξ : V => (1 + ‖ξ‖) ^ J * ‖𝓕 f ξ‖) :=
    (henv.const_mul C).mono' hmeas (ae_of_all _ (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound ξ))
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ ξ : V, C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := integral_mono hInt (henv.const_mul C) hbound
    _ = _ := by rw [integral_const_mul]; unfold weightedFourierL1Constant C; ring

end WaveTurbulence.Incoh
