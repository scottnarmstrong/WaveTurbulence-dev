/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.PoissonMultidimensional
public import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Absolute Poisson majorants for the sumint cutoff amplitudes

The Fourier-side lattice series is absolutely summable because the
amplitude is Schwartz. The majorant therefore bounds a substantive sum,
with no reliance on totalization of divergent series.
-/

public section

open scoped SchwartzMap ContDiff

namespace WaveTurbulence.Sumint

/-- Samples of a Schwartz function on every nonzero scaled lattice are summable. -/
theorem schwartz_scaled_samples_summable {n : ℕ} (f : 𝓢((Fin n → ℝ), ℂ))
    {L : ℝ} (hL : L ≠ 0) : Summable (fun m : Fin n → ℤ => f (fun j => L * (m j : ℝ))) := by
  have h := Fourier.schwartz_lattice_summable
    (Fourier.schwartzCoordinateDilate (inv_ne_zero hL) f)
  simp only [Fourier.schwartzCoordinateDilate_apply, inv_inv] at h
  apply h.congr
  intro m
  congr 1

/-- Absolute summability of the exact scaled Fourier samples in Poisson summation. -/
theorem fourier_scaled_samples_summable {n : ℕ} (f : 𝓢((Fin n → ℝ), ℂ))
    {L : ℝ} (hL : L ≠ 0) :
    Summable (fun m : Fin n → ℤ => ‖Fourier.timeFourier f (fun j => L * (m j : ℝ))‖) := by
  simpa only [Fourier.coordinateFourierSchwartz_apply] using
    (schwartz_scaled_samples_summable (Fourier.coordinateFourierSchwartz f) hL).norm

/-- The norm of a scaled lattice sum is bounded by its absolutely convergent Poisson majorant. -/
theorem norm_lattice_sum_le_poisson {n : ℕ} (f : 𝓢((Fin n → ℝ), ℂ))
    {L : ℝ} (hL : 0 < L) :
    ‖∑' m : Fin n → ℤ, f (fun j => (m j : ℝ) / L)‖ ≤
      L^n * ∑' m : Fin n → ℤ, ‖Fourier.timeFourier f (fun j => L * (m j : ℝ))‖ := by
  rw [Fourier.poisson_scaled_coordinates f hL, norm_mul]
  have hc : ‖(L^n : ℂ)‖ = L^n := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hL.le _)
  exact norm_tsum_le_tsum_norm (fourier_scaled_samples_summable f hL.ne')

/-- Smooth compact cutoff amplitudes inherit the same absolute Poisson bound. -/
theorem norm_lattice_sum_le_poisson_smooth_compact {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {L : ℝ} (hL : 0 < L) :
    ‖∑' m : Fin n → ℤ, f (fun j => (m j : ℝ) / L)‖ ≤
      L^n * ∑' m : Fin n → ℤ, ‖Fourier.timeFourier f (fun j => L * (m j : ℝ))‖ :=
  norm_lattice_sum_le_poisson (hc.toSchwartzMap hf) hL

end WaveTurbulence.Sumint
