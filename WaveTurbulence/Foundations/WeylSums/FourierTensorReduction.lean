/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CompactFourier
public import WaveTurbulence.Foundations.WeylSums.HuaOrthogonality
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Fourier reduction to products of one-dimensional quadratic sums

The finite coordinate types can be intervals, parity classes, or arbitrary
finite lattice pieces. Fourier decomposition shifts only the linear
frequencies. No product assumption is imposed on the original joint cutoff.
-/

public section
open MeasureTheory Finset
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- Tensorization of a separated quadratic phase on a finite lattice box. -/
theorem finite_quadratic_tensor {m : ℕ} {κ : Fin m → Type*} [∀ i, Fintype (κ i)]
    (θ : ∀ i, κ i → ℂ) (x : ∀ i, κ i → ℝ) (s r : Fin m → ℝ) :
    (∑ v : ∀ i, κ i, (∏ i, θ i (v i)) *
      e (∑ i, (s i * (x i (v i))^2 + r i * x i (v i)))) =
      ∏ i, ∑ j, θ i j * e (s i * (x i j)^2 + r i * x i j) := by
  simp_rw [e_sum, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => θ i j * e (s i * (x i j)^2 + r i * x i j))).symm

/-- An integrable Fourier weight reduces a joint cutoff sum to a product
of one-dimensional sums, with all Fourier frequencies shifted explicitly. -/
theorem fourier_tensor_reduction {m : ℕ} {κ : Fin m → Type*} [∀ i, Fintype (κ i)]
    (F : EuclideanSpace ℝ (Fin m) → ℂ) (hF : Integrable F)
    (θ : ∀ i, κ i → ℂ) (x : ∀ i, κ i → ℝ) (s r : Fin m → ℝ) :
    (∑ v : ∀ i, κ i, (∏ i, θ i (v i)) *
      (∫ ξ, F ξ * e (∑ i, (ξ i * x i (v i)))) *
      e (∑ i, (s i * (x i (v i))^2 + r i * x i (v i)))) =
      ∫ ξ : EuclideanSpace ℝ (Fin m), F ξ *
        ∏ i, ∑ j, θ i j * e (s i * (x i j)^2 + (r i + ξ i) * x i j) := by
  classical
  let A (v : ∀ i, κ i) (ξ : EuclideanSpace ℝ (Fin m)) : ℂ :=
    (∏ i, θ i (v i)) * (F ξ * e (∑ i, (ξ i * x i (v i)))) *
      e (∑ i, (s i * (x i (v i))^2 + r i * x i (v i)))
  have hint (v : ∀ i, κ i) : Integrable (A v) := by
    apply Integrable.mul_const
    apply Integrable.const_mul
    apply hF.mul_bdd
    · exact (continuous_e.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ξ => (norm_e _).le)
  have hterm (v : ∀ i, κ i) :
      (∏ i, θ i (v i)) * (∫ ξ, F ξ * e (∑ i, (ξ i * x i (v i)))) *
        e (∑ i, (s i * (x i (v i))^2 + r i * x i (v i))) = ∫ ξ, A v ξ := by
    dsimp [A]
    rw [integral_mul_const, integral_const_mul]
  simp_rw [hterm]
  rw [← integral_finsetSum _ (fun v _ => hint v)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← finite_quadratic_tensor θ x s (fun i => r i + ξ i), mul_sum]
  apply sum_congr rfl
  intro v hv
  have heq : e (∑ i, ξ i * x i (v i)) *
      e (∑ i, (s i * (x i (v i))^2 + r i * x i (v i))) =
      e (∑ i, (s i * (x i (v i))^2 + (r i + ξ i) * x i (v i))) := by
    rw [← e_add, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring
  calc
    _ = F ξ * (∏ i, θ i (v i)) *
        (e (∑ i, ξ i * x i (v i)) * e (∑ i, (s i * (x i (v i))^2 + r i * x i (v i)))) := by
      dsimp [A]
      ring
    _ = _ := by rw [heq]; ring

/-- Uniform one-dimensional bounds pass through an arbitrary integrable
Fourier superposition at the cost of the `L¹` norm of its weight. -/
theorem norm_fourier_tensor_reduction_le {m : ℕ} {κ : Fin m → Type*} [∀ i, Fintype (κ i)]
    (F : EuclideanSpace ℝ (Fin m) → ℂ) (hF : Integrable F)
    (θ : ∀ i, κ i → ℂ) (x : ∀ i, κ i → ℝ) (s r B : Fin m → ℝ)
    (_hB : ∀ i, 0 ≤ B i)
    (hb : ∀ i ρ, ‖∑ j, θ i j * e (s i * (x i j)^2 + ρ * x i j)‖ ≤ B i) :
    ‖∑ v : ∀ i, κ i, (∏ i, θ i (v i)) *
      (∫ ξ, F ξ * e (∑ i, (ξ i * x i (v i)))) *
      e (∑ i, (s i * (x i (v i))^2 + r i * x i (v i)))‖ ≤
      (∫ ξ, ‖F ξ‖) * ∏ i, B i := by
  rw [fourier_tensor_reduction F hF θ x s r]
  have hh : ‖∫ ξ : EuclideanSpace ℝ (Fin m), F ξ *
      ∏ i, ∑ j, θ i j * e (s i * (x i j)^2 + (r i + ξ i) * x i j)‖ ≤
      ∫ ξ : EuclideanSpace ℝ (Fin m), ‖F ξ‖ * ∏ i, B i := by
    apply norm_integral_le_of_norm_le (hF.norm.mul_const _)
    filter_upwards [] with ξ
    rw [norm_mul, norm_prod]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hb i _)
  simpa only [integral_mul_const] using hh

end WaveTurbulence.WeylSums
