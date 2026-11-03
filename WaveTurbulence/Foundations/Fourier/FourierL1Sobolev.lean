/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic

/-!
# A Fourier-L¹ estimate from integrable derivatives

The one-factor estimate used in TARGET L1007–L1012: `d+1` integrable
Fréchet derivatives suffice in dimension `d`. The Sobolev expression is
an operator-norm version of `W^{d+1,1}`. Its comparison with coordinate
partial-derivative norms involves only dimension-dependent constants.
-/

public section

open MeasureTheory Module
open scoped FourierTransform

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The sum of the `L¹` operator norms of derivatives up to order `N`.
The estimates using it explicitly assume these derivatives are integrable. -/
@[expose] noncomputable def derivativeL1Sum (N : ℕ) (f : V → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖

theorem derivativeL1Sum_nonneg (N : ℕ) (f : V → ℂ) :
    0 ≤ derivativeL1Sum N f :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

private theorem integral_norm_le_derivativeL1Sum (N : ℕ) (f : V → ℂ) :
    (∫ x, ‖f x‖) ≤ derivativeL1Sum N f := by
  have h := Finset.single_le_sum
    (s := Finset.range (N + 1)) (a := 0)
    (f := fun j => ∫ x, ‖iteratedFDeriv ℝ j f x‖)
    (fun _ _ => integral_nonneg fun _ => norm_nonneg _) (by simp)
  simpa only [norm_iteratedFDeriv_zero, derivativeL1Sum] using h

/-- Polynomial decay with an explicit Sobolev expression, uniform in `ξ`. -/
theorem fourier_polynomial_weight_le {N : ℕ} {f : V → ℂ}
    (hf : ContDiff ℝ N f) (hi : ∀ j ≤ N, Integrable (iteratedFDeriv ℝ j f)) (ξ : V) :
    (1 + ‖ξ‖) ^ N * ‖𝓕 f ξ‖ ≤
      (2 : ℝ) ^ (N - 1) * (1 + 2 ^ N) * derivativeL1Sum N f := by
  have hdec := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := N)
    hf (fun k n hk hn => by
      have hk0 : k = 0 := by
        have : k ≤ 0 := by exact_mod_cast hk
        omega
      subst k
      simpa using (hi n (by exact_mod_cast hn)).norm)
    (k := 0) (n := N) (by simp) (by simp) ξ
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul,
    Nat.cast_zero, mul_zero, zero_add, Finset.range_one,
    Finset.sum_product, Finset.sum_singleton] at hdec
  have hnorm := (Real.norm_fourier_le_integral_norm f ξ).trans
    (integral_norm_le_derivativeL1Sum N f)
  calc
    _ ≤ (2 : ℝ) ^ (N - 1) * ((1 + ‖ξ‖ ^ N) * ‖𝓕 f ξ‖) := by
      simpa only [one_pow, mul_assoc] using
        mul_le_mul_of_nonneg_right (add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
          (norm_nonneg ξ) N) (norm_nonneg (𝓕 f ξ))
    _ ≤ (2 : ℝ) ^ (N - 1) * ((1 + 2 ^ N) * derivativeL1Sum N f) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change _ ≤ _ at hdec
      dsimp [derivativeL1Sum] at hnorm ⊢
      nlinarith only [hnorm, hdec]
    _ = _ := by ring

/-- The dimension-dependent absolute Fourier-L¹ constant for `N` derivatives.
It is finite whenever `N > dim V`. -/
@[expose] noncomputable def fourierL1Constant (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (N - 1) * (1 + 2 ^ N) * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(N : ℝ))

/-- Nonnegativity of the dimension-dependent Fourier-L¹ constant. -/
theorem fourierL1Constant_nonneg (N : ℕ) : 0 ≤ fourierL1Constant V N :=
  mul_nonneg (by positivity) (integral_nonneg fun ξ => Real.rpow_nonneg (by positivity) _)

/-- `W^{N,1}` controls the Fourier-L¹ norm when `N` exceeds the dimension.
All constants depend only on the ambient space and derivative order. -/
theorem fourier_integrable_and_integral_norm_le {N : ℕ} {f : V → ℂ}
    (hN : finrank ℝ V < N) (hf : ContDiff ℝ N f)
    (hi : ∀ j ≤ N, Integrable (iteratedFDeriv ℝ j f)) :
    Integrable (𝓕 f) ∧ (∫ ξ, ‖𝓕 f ξ‖) ≤ fourierL1Constant V N * derivativeL1Sum N f := by
  have henv : Integrable (fun ξ : V => (1 + ‖ξ‖) ^ (-(N : ℝ))) :=
    integrable_one_add_norm (by exact_mod_cast hN)
  have hbound (ξ : V) : ‖𝓕 f ξ‖ ≤
      ((2 : ℝ) ^ (N - 1) * (1 + 2 ^ N) * derivativeL1Sum N f) *
        (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
    have h := fourier_polynomial_weight_le hf hi ξ
    have hp : 0 < (1 + ‖ξ‖) ^ N := pow_pos (by positivity) _
    have hh : ‖𝓕 f ξ‖ ≤
        ((2 : ℝ) ^ (N - 1) * (1 + 2 ^ N) * derivativeL1Sum N f) / (1 + ‖ξ‖) ^ N :=
      (le_div_iff₀ hp).2 (by simpa only [mul_comm] using h)
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hfi : Integrable f := by
    have h : Integrable (fun x => ‖f x‖) := by
      simpa only [norm_iteratedFDeriv_zero] using (hi 0 (Nat.zero_le _)).norm
    exact (integrable_norm_iff hf.continuous.aestronglyMeasurable).mp h
  have hF : Integrable (𝓕 f) :=
    (henv.const_mul _).mono' (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hfi).aestronglyMeasurable
      (ae_of_all _ hbound)
  refine ⟨hF, ?_⟩
  calc
    (∫ ξ, ‖𝓕 f ξ‖) ≤ ∫ ξ : V,
        ((2 : ℝ) ^ (N - 1) * (1 + 2 ^ N) * derivativeL1Sum N f) *
          (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
      integral_mono hF.norm (henv.const_mul _) hbound
    _ = _ := by rw [integral_const_mul]; unfold fourierL1Constant; ring

end WaveTurbulence.Fourier
