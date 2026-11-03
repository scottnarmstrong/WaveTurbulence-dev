/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Interchanging Gaussian quadratic sums and Fourier superpositions

Absolute summability is controlled by the Gaussian weight times the `L¹`
norm of the Fourier weight. This justifies the superposition argument for
generic smooth cutoffs without any conditional convergence assumptions.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace WaveTurbulence.WeylSums

theorem continuous_e : Continuous e := by
  unfold e
  fun_prop

/-- A unit additive phase does not change the Gaussian norm. -/
theorem norm_gaussianWeight_mul_e (L x t : ℝ) :
    ‖(gaussianWeight L x : ℂ) * e t‖ = gaussianWeight L x := by
  rw [norm_mul, norm_e, mul_one]
  exact Complex.norm_of_nonneg (Real.exp_pos _).le

/-- Summability of the real Gaussian weight at positive scale. -/
theorem summable_gaussianWeight {L : ℝ} (hL : 0 < L) :
    Summable (fun n : ℤ => gaussianWeight L n) := by
  apply (summable_gaussianQuadraticTerm hL 0 0).norm.congr
  intro n
  exact norm_gaussianWeight_mul_e L n _

/-- Interchange an integrable Fourier superposition with a Gaussian quadratic
sum. The hypotheses concern only the weight and positive scale. -/
theorem hasSum_gaussian_fourier (F : ℝ → ℂ) (hF : Integrable F)
    {L : ℝ} (hL : 0 < L) (s r : ℝ) :
    HasSum (fun n : ℤ => (gaussianWeight L n : ℂ) *
      (∫ ξ : ℝ, F ξ * e (ξ * ((n : ℝ) / L))) * e (s * (n : ℝ) ^ 2 + r * n))
      (∫ ξ : ℝ, F ξ * gaussianQuadraticSum L s (r + ξ / L)) := by
  let A : ℤ → ℝ → ℂ := fun n ξ => F ξ *
    ((gaussianWeight L n : ℂ) * e (s * (n : ℝ) ^ 2 + (r + ξ / L) * n))
  have hnorm (n : ℤ) (ξ : ℝ) : ‖A n ξ‖ = ‖F ξ‖ * gaussianWeight L n := by
    dsimp only [A]
    rw [norm_mul, norm_gaussianWeight_mul_e]
  have hInt (n : ℤ) : Integrable (A n) := by
    apply hF.mul_bdd
    · apply Continuous.aestronglyMeasurable
      exact continuous_const.mul (continuous_e.comp (by fun_prop))
    · exact Filter.Eventually.of_forall (fun ξ => (norm_gaussianWeight_mul_e L n _).le)
  have hIntNorm (n : ℤ) : (∫ ξ : ℝ, ‖A n ξ‖) = (∫ ξ : ℝ, ‖F ξ‖) * gaussianWeight L n := by
    simp_rw [hnorm]
    exact integral_mul_const _ _
  have hSum : Summable (fun n : ℤ => ∫ ξ : ℝ, ‖A n ξ‖) := by
    simp_rw [hIntNorm]
    exact (summable_gaussianWeight hL).mul_left _
  have hterm (n : ℤ) : (∫ ξ : ℝ, A n ξ) =
      (gaussianWeight L n : ℂ) * (∫ ξ : ℝ, F ξ * e (ξ * ((n : ℝ) / L))) *
        e (s * (n : ℝ) ^ 2 + r * n) := by
    let c : ℂ := (gaussianWeight L n : ℂ) * e (s * (n : ℝ) ^ 2 + r * n)
    have hphase (ξ : ℝ) : e (s * (n : ℝ) ^ 2 + (r + ξ / L) * n) =
        e (ξ * ((n : ℝ) / L)) * e (s * (n : ℝ) ^ 2 + r * n) := by
      rw [← e_add]
      congr 1
      ring
    calc
      _ = ∫ ξ : ℝ, c * (F ξ * e (ξ * ((n : ℝ) / L))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ξ => by dsimp [A, c]; rw [hphase]; ring)
      _ = c * ∫ ξ : ℝ, F ξ * e (ξ * ((n : ℝ) / L)) := integral_const_mul _ _
      _ = _ := by dsimp [c]; ring
  have hh := hasSum_integral_of_summable_integral_norm hInt hSum
  have hrhs : (∫ ξ : ℝ, ∑' n : ℤ, A n ξ) =
      ∫ ξ : ℝ, F ξ * gaussianQuadraticSum L s (r + ξ / L) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by dsimp [A, gaussianQuadraticSum]; rw [tsum_mul_left])
  rw [hrhs] at hh
  convert hh using 1
  funext n
  exact (hterm n).symm

/-- Integral form of the absolutely convergent Gaussian superposition. -/
theorem gaussian_fourier_sum_integral (F : ℝ → ℂ) (hF : Integrable F)
    {L : ℝ} (hL : 0 < L) (s r : ℝ) :
    (∑' n : ℤ, (gaussianWeight L n : ℂ) * (∫ ξ : ℝ, F ξ * e (ξ * ((n : ℝ) / L))) *
      e (s * (n : ℝ) ^ 2 + r * n)) =
      ∫ ξ : ℝ, F ξ * gaussianQuadraticSum L s (r + ξ / L) :=
  (hasSum_gaussian_fourier F hF hL s r).tsum_eq

end WaveTurbulence.WeylSums
