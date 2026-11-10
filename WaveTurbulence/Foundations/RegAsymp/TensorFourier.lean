/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.FourierModulation
public import WaveTurbulence.Foundations.ApproxNT.PsiOne
public import WaveTurbulence.Foundations.ApproxNT.Statement
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Exact Fourier factorization in fixed-dimensional momentum blocks -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped FourierTransform

/-- Independent spatial profiles Fourier transform block by block.
No Sobolev derivative order depends on the number of blocks. -/
theorem tensor_fourier_factorization {ι : Type*} [Fintype ι] {d : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin d) → ℂ) (ξ : ι → EuclideanSpace ℝ (Fin d)) :
    (∫ x : ι → EuclideanSpace ℝ (Fin d),
      Real.fourierChar (-(∑ i, inner ℝ (x i) (ξ i))) • ∏ i, f i (x i)) =
        ∏ i, 𝓕 (f i) (ξ i) := by
  simp_rw [Circle.smul_def,smul_eq_mul,← Finset.sum_neg_distrib,
    ApproxNT.fourierChar_finset_sum,← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod
    (fun i x => (Real.fourierChar (-inner ℝ x (ξ i)) : ℂ) * f i x)]
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul]

/-- The two-array Fourier transform in the exact NT convention factors
into the actual fixed-dimensional transforms of the input profiles. -/
theorem fourierW_tensor_factorization {d n : ℕ}
    (f g : Fin n → EuclideanSpace ℝ (Fin d) → ℂ)
    (ξ η : Fin n → EuclideanSpace ℝ (Fin d)) :
    ApproxNT.fourierW (fun x y => (∏ j, f j (x j))*(∏ j, g j (y j))) ξ η =
      (∏ j, 𝓕 (f j) (ξ j))*(∏ j, 𝓕 (g j) (η j)) := by
  unfold ApproxNT.fourierW
  have hp (z : (Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → EuclideanSpace ℝ (Fin d))) :
      Real.fourierChar (-(∑ j, (inner ℝ (z.1 j) (ξ j)+inner ℝ (z.2 j) (η j)))) •
        ((∏ j, f j (z.1 j))*(∏ j, g j (z.2 j))) =
      (Real.fourierChar (-(∑ j, inner ℝ (z.1 j) (ξ j))) • ∏ j, f j (z.1 j)) *
        (Real.fourierChar (-(∑ j, inner ℝ (z.2 j) (η j))) • ∏ j, g j (z.2 j)) := by
    rw [Finset.sum_add_distrib,neg_add,AddChar.map_add_eq_mul]
    simp only [Circle.smul_def,smul_eq_mul,Circle.coe_mul]
    ring
  simp_rw [hp]
  change (∫ z : (Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → EuclideanSpace ℝ (Fin d)),
    (Real.fourierChar (-(∑ j, inner ℝ (z.1 j) (ξ j))) • ∏ j, f j (z.1 j)) *
      (Real.fourierChar (-(∑ j, inner ℝ (z.2 j) (η j))) • ∏ j, g j (z.2 j))
      ∂((volume : Measure (Fin n → EuclideanSpace ℝ (Fin d))).prod volume)) = _
  rw [integral_prod_mul (μ := volume) (ν := volume)
    (fun x : Fin n → EuclideanSpace ℝ (Fin d) =>
      Real.fourierChar (-(∑ j, inner ℝ (x j) (ξ j))) • ∏ j, f j (x j))
    (fun y : Fin n → EuclideanSpace ℝ (Fin d) =>
      Real.fourierChar (-(∑ j, inner ℝ (y j) (η j))) • ∏ j, g j (y j))]
  rw [tensor_fourier_factorization f ξ,tensor_fourier_factorization g η]

end WaveTurbulence.RegAsymp
