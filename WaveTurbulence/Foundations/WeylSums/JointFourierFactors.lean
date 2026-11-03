/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianSuperposition
public import WaveTurbulence.Foundations.WeylSums.HuaOrthogonality
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fintype.Pi

/-!
# Fourier factorization on arbitrary finite coordinate blocks

A block can be a pair or triple of integer variables, including its parity
constraint. The spatial insertion maps and phase functions are arbitrary;
quadratic structure is used only when proving the individual block bounds.
-/

public section
open MeasureTheory Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- Fourier superposition factorizes over finite blocks and shifts each
block's phase by the corresponding linear Fourier functional. -/
theorem joint_fourier_factorization {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (F : EuclideanSpace ℝ J → ℂ) (hF : Integrable F)
    (θ : ∀ i, κ i → ℂ) (X : ∀ i, κ i → EuclideanSpace ℝ J) (φ : ∀ i, κ i → ℝ) :
    (∑ v : ∀ i, κ i, (∏ i, θ i (v i)) *
      (∫ ξ, F ξ * e (inner ℝ ξ (∑ i, X i (v i)))) * e (∑ i, φ i (v i))) =
      ∫ ξ : EuclideanSpace ℝ J, F ξ *
        ∏ i, ∑ a, θ i a * e (φ i a + inner ℝ ξ (X i a)) := by
  classical
  let A (v : ∀ i, κ i) (ξ : EuclideanSpace ℝ J) : ℂ :=
    (∏ i, θ i (v i)) * (F ξ * e (inner ℝ ξ (∑ i, X i (v i)))) * e (∑ i, φ i (v i))
  have hint (v : ∀ i, κ i) : Integrable (A v) := by
    apply Integrable.mul_const
    apply Integrable.const_mul
    apply hF.mul_bdd
    · exact (continuous_e.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ξ => (norm_e _).le)
  have hterm (v : ∀ i, κ i) :
      (∏ i, θ i (v i)) * (∫ ξ, F ξ*e (inner ℝ ξ (∑ i, X i (v i)))) * e (∑ i, φ i (v i)) =
        ∫ ξ, A v ξ := by
    dsimp [A]
    rw [integral_mul_const, integral_const_mul]
  simp_rw [hterm]
  rw [← integral_finsetSum _ (fun v hv => hint v)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hphase (v : ∀ i, κ i) :
      inner ℝ ξ (∑ i, X i (v i)) + (∑ i, φ i (v i)) =
        ∑ i, (φ i (v i)+inner ℝ ξ (X i (v i))) := by
    rw [inner_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  have halg : (∑ v : ∀ i, κ i, A v ξ) = F ξ *
      ∑ v : ∀ i, κ i, ∏ i, θ i (v i) * e (φ i (v i)+inner ℝ ξ (X i (v i))) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro v hv
    rw [prod_mul_distrib, ← e_sum]
    dsimp [A]
    rw [← hphase]
    rw [e_add]
    ring
  rw [halg]
  congr 1
  exact (Fintype.prod_sum (fun i a => θ i a * e (φ i a + inner ℝ ξ (X i a)))).symm

/-- Integrating an arbitrary joint Fourier weight costs its `L¹` norm times
the product of uniform block bounds. The source applications prove each
block bound from the one-dimensional Gauss estimate and parity averaging. -/
theorem norm_joint_fourier_factorization_le {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (F : EuclideanSpace ℝ J → ℂ) (hF : Integrable F)
    (θ : ∀ i, κ i → ℂ) (X : ∀ i, κ i → EuclideanSpace ℝ J) (φ : ∀ i, κ i → ℝ)
    (B : ι → ℝ)
    (hb : ∀ ξ : EuclideanSpace ℝ J, ∀ i, ‖∑ a, θ i a*e (φ i a+inner ℝ ξ (X i a))‖ ≤ B i) :
    ‖∑ v : ∀ i, κ i, (∏ i, θ i (v i)) *
      (∫ ξ, F ξ*e (inner ℝ ξ (∑ i, X i (v i)))) * e (∑ i, φ i (v i))‖ ≤
      (∫ ξ, ‖F ξ‖) * ∏ i, B i := by
  rw [joint_fourier_factorization F hF θ X φ]
  have hh : ‖∫ ξ : EuclideanSpace ℝ J, F ξ *
      ∏ i, ∑ a, θ i a*e (φ i a+inner ℝ ξ (X i a))‖ ≤
      ∫ ξ : EuclideanSpace ℝ J, ‖F ξ‖ * ∏ i, B i := by
    apply norm_integral_le_of_norm_le (hF.norm.mul_const _)
    filter_upwards [] with ξ
    rw [norm_mul, norm_prod]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact prod_le_prod₀ (fun i hi => norm_nonneg _) (fun i hi => hb ξ i)
  simpa only [integral_mul_const] using hh

end WaveTurbulence.WeylSums
