/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ScalarFourierMass
public import WaveTurbulence.Foundations.SumintPar.ProductMeasureTools

/-!
# Tensor-product cutoff norms from scalar weighted Fourier masses

One scalar bracket weight in each coordinate controls every maximum-
bracket exponent at most one. Exact coordinate Fourier factorization
and nonnegative Fubini then give the product of scalar masses.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
open scoped FourierTransform Classical
namespace WaveTurbulence.SumintPar

/-- The native maximum bracket is bounded by the product of the scalar coordinate brackets. -/
theorem timeBracket_le_scalarBracket_product {r : ℕ} (ξ : Fin r → ℝ) :
    Fourier.timeBracket ξ ≤ ∏ j : Fin r, scalarBracket (ξ j) := by
  apply Fourier.timeBracket_le (Finset.one_le_prod₀ (fun _ _ => one_le_scalarBracket _))
  intro j
  have he := Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ ({j}:Finset (Fin r)))
    (fun k _ => zero_le_one.trans (one_le_scalarBracket (ξ k))) (fun k _ _ => one_le_scalarBracket (ξ k))
  change scalarBracket (ξ j) ≤ ∏ k : Fin r, scalarBracket (ξ k)
  simpa only [Finset.prod_singleton] using he

/-- A tensor cutoff's native weighted norm is bounded by the product of its scalar weighted masses. -/
theorem timeFourierNorm_tensor_le_scalarMass {r : ℕ} {θ : ℝ} (hθ : θ ≤ 1)
    (f : Fin r → ℝ → ℂ) (hf : ∀ j, Integrable (f j)) :
    Fourier.timeFourierNorm θ (fun t : Fin r → ℝ => ∏ j, f j (t j)) ≤ ∏ j, scalarFourierMass (f j) := by
  have hi : Integrable (fun t : Fin r → ℝ => ∏ j, f j (t j)) := Integrable.fintype_prod hf
  have hft (j : Fin r) : Measurable (𝓕 (f j)) :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (hf j)).measurable
  have hb : Continuous scalarBracket := by unfold scalarBracket; fun_prop
  rw [Fourier.timeFourierNorm_eq_lintegral hi]
  calc
    _ ≤ ∫⁻ ξ : Fin r → ℝ, ∏ j, ENNReal.ofReal (scalarBracket (ξ j))*‖𝓕 (f j) (ξ j)‖ₑ := by
      apply lintegral_mono
      intro ξ
      change Fourier.timeWeight θ ξ*‖Fourier.timeFourier (fun t : Fin r → ℝ => ∏ j, f j (t j)) ξ‖ₑ ≤
        ∏ j, ENNReal.ofReal (scalarBracket (ξ j))*‖𝓕 (f j) (ξ j)‖ₑ
      rw [Fourier.timeFourier_coordinate_product,← ofReal_norm,norm_prod,
        ENNReal.ofReal_prod_of_nonneg (fun j _ => norm_nonneg _)]
      simp only [ofReal_norm]
      rw [Finset.prod_mul_distrib]
      apply mul_le_mul' _ le_rfl
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => zero_le_one.trans (one_le_scalarBracket _))]
      apply ENNReal.ofReal_le_ofReal
      exact (Real.rpow_le_rpow_of_exponent_le (Fourier.one_le_timeBracket ξ) hθ).trans
        ((Real.rpow_one _).le.trans (timeBracket_le_scalarBracket_product ξ))
    _ = _ := lintegral_fintype_prod_eq_prod _ _
      (fun j => hb.measurable.ennreal_ofReal.mul (hft j).enorm)

end WaveTurbulence.SumintPar
