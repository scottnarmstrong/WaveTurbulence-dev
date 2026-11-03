/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic

/-!
# Uniform non-stationary phase for translated smooth cutoffs

TARGET L966, L1550. Translation only changes the Fourier transform by a
unit complex phase. Schwartz seminorms of the fixed amplitude's Fourier
transform give rapid decay uniformly in the translation parameter.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- An explicit rapid-decay constant for a fixed Schwartz amplitude. -/
@[expose] noncomputable def nonstationaryConstant (N : ℕ) (f : 𝓢(V, ℂ)) : ℝ :=
  (2 : ℝ) ^ (N - 1) * (SchwartzMap.seminorm ℂ 0 0 (𝓕 f) +
    SchwartzMap.seminorm ℂ N 0 (𝓕 f))

theorem nonstationaryConstant_nonneg (N : ℕ) (f : 𝓢(V, ℂ)) :
    0 ≤ nonstationaryConstant N f := by
  apply mul_nonneg (by positivity)
  exact add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)

private theorem schwartz_fourier_weight_le (N : ℕ) (f : 𝓢(V, ℂ)) (w : V) :
    (1 + ‖w‖) ^ N * ‖𝓕 f w‖ ≤ nonstationaryConstant N f := by
  have h0 := SchwartzMap.norm_le_seminorm ℂ (𝓕 f) w
  have hN := SchwartzMap.norm_pow_mul_le_seminorm ℂ (𝓕 f) N w
  calc
    _ ≤ (2 : ℝ) ^ (N - 1) * ((1 + ‖w‖ ^ N) * ‖𝓕 f w‖) := by
      simpa only [one_pow, mul_assoc] using mul_le_mul_of_nonneg_right
        (add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg w) N) (norm_nonneg (𝓕 f w))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [h0, hN]

/-- Translation of an amplitude preserves the absolute Fourier integral. -/
theorem norm_oscillatory_translate_eq (f : V → ℂ) (a w : V) :
    ‖∫ x, Real.fourierChar (inner ℝ x w) • f (x - a)‖ = ‖𝓕 f (-w)‖ := by
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ V) f (-a)) (-w)
  have hn := congrArg norm ht
  simpa only [VectorFourier.fourierIntegral, Function.comp_apply, innerₗ_apply_apply, inner_neg_right,
    neg_neg, ← sub_eq_add_neg, Circle.norm_smul, Real.fourier_eq] using hn

/-- TARGET L966, L1550: rapid decay uniformly in the translation `a`.
The fixed-amplitude constant is displayed as Schwartz seminorms. -/
theorem nonstationary_phase (N : ℕ) (f : 𝓢(V, ℂ)) (a w : V) :
    ‖∫ x, Real.fourierChar (inner ℝ x w) • f (x - a)‖ ≤
      nonstationaryConstant N f / (1 + ‖w‖) ^ N := by
  rw [norm_oscillatory_translate_eq]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖w‖) N)).mpr
  simpa only [norm_neg, mul_comm, SchwartzMap.fourier_coe] using schwartz_fourier_weight_le N f (-w)

/-- The Japanese-bracket version of the non-stationary phase estimate. -/
theorem nonstationary_phase_japanese (N : ℕ) (f : 𝓢(V, ℂ)) (a w : V) :
    ‖∫ x, Real.fourierChar (inner ℝ x w) • f (x - a)‖ ≤
      nonstationaryConstant N f / Real.sqrt (1 + ‖w‖ ^ 2) ^ N := by
  apply (nonstationary_phase N f a w).trans
  apply div_le_div_of_nonneg_left (nonstationaryConstant_nonneg N f)
    (pow_pos (Real.sqrt_pos.mpr (by positivity)) N)
  apply pow_le_pow_left₀ (Real.sqrt_nonneg _) _ N
  have hs := Real.sq_sqrt (show 0 ≤ 1 + ‖w‖ ^ 2 by positivity)
  have hn := norm_nonneg w
  have hr := Real.sqrt_nonneg (1 + ‖w‖ ^ 2)
  nlinarith

end WaveTurbulence.Fourier
