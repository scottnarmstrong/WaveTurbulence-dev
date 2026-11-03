/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeFourier
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Products of one-dimensional Fourier transforms

The coordinate Fourier transform factors exactly on products. This
identifies the two-time Duhamel kernel as a tensor product.
-/

public section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace WaveTurbulence.Fourier

private theorem fourierChar_finite_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (Real.fourierChar (∑ i ∈ s, a i) : ℂ) = ∏ i ∈ s, (Real.fourierChar (a i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, Circle.coe_mul, ih]

/-- Exact factorization on an arbitrary finite product of scalar functions. -/
theorem timeFourier_coordinate_product {r : ℕ} (f : Fin r → ℝ → ℂ) (ξ : Fin r → ℝ) :
    timeFourier (fun t => ∏ j, f j (t j)) ξ = ∏ j, 𝓕 (f j) (ξ j) := by
  unfold timeFourier VectorFourier.fourierIntegral timePairing
  change (∫ t : Fin r → ℝ, Real.fourierChar (-(∑ j, t j * ξ j)) • ∏ j, f j (t j)) = _
  simp_rw [Circle.smul_def, smul_eq_mul, ← Finset.sum_neg_distrib,
    fourierChar_finite_sum, ← Finset.prod_mul_distrib]
  change (∫ t : Fin r → ℝ, ∏ j, (Real.fourierChar (-(t j * ξ j)) : ℂ) * f j (t j)) = _
  calc
    _ = ∏ j, ∫ u : ℝ, (Real.fourierChar (-(u * ξ j)) : ℂ) * f j u :=
      integral_fin_nat_prod_volume_eq_prod (fun j u =>
        (Real.fourierChar (-(u * ξ j)) : ℂ) * f j u)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      rw [Real.fourier_eq]
      simp only [Circle.smul_def, smul_eq_mul, RCLike.inner_apply', conj_trivial, mul_comm]

end WaveTurbulence.Fourier
