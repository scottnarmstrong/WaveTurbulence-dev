/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.PoissonCoefficients
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Multidimensional Poisson summation

TARGET L1035, L1541, L1575. For `L⁻¹ℤ^d` the dual lattice is `Lℤ^d`
and the volume factor is `L^d`. The statement applies to arbitrary Schwartz
amplitudes, including amplitudes that do not factor by coordinate.
-/

public section

open MeasureTheory
open scoped SchwartzMap ContDiff

namespace WaveTurbulence.Fourier

/-- Poisson summation on `ℤ^d`, in the paper's Fourier convention. -/
theorem poisson_integer {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ)) :
    (∑' n : Fin d → ℤ, f (fun i => (n i : ℝ))) =
      ∑' m : Fin d → ℤ, timeFourier f (fun i => (m i : ℝ)) := by
  have hs : Summable (WaveTurbulence.torusFourierCoeff 1 (schwartzPeriodization f)) := by
    change Summable (fun m => WaveTurbulence.torusFourierCoeff 1 (schwartzPeriodization f) m)
    simp_rw [torusFourierCoeff_schwartzPeriodization]
    exact coordinateFourier_lattice_summable f
  have h := WaveTurbulence.hasSum_torusFourier_series_of_summable (by norm_num : (0 : ℝ) < 1)
    (schwartzPeriodization f).continuous (schwartzPeriodization_periodic f) hs (0 : Fin d → ℝ)
  simpa [schwartzPeriodization_apply, torusFourierCoeff_schwartzPeriodization,
    WaveTurbulence.torusChar] using h.tsum_eq.symm

/-- Fourier scaling in any finite coordinate dimension. -/
theorem timeFourier_comp_inv_smul {d : ℕ} (f : (Fin d → ℝ) → ℂ)
    {L : ℝ} (hL : 0 < L) (ξ : Fin d → ℝ) :
    timeFourier (fun x => f (L⁻¹ • x)) ξ = (L ^ d : ℝ) • timeFourier f (L • ξ) := by
  let g := fun x => Real.fourierChar (-timePairing d x (L • ξ)) • f x
  have h := Measure.integral_comp_inv_smul volume g L
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (pow_nonneg hL.le _)] at h
  change (∫ x, Real.fourierChar (-timePairing d x ξ) • f (L⁻¹ • x)) =
    (L ^ d : ℝ) • ∫ x, g x
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only [g]
    congr 2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp [hL.ne']

/-- Pulling back by a nonzero scalar dilation preserves the coordinate Schwartz class. -/
@[expose] noncomputable def schwartzCoordinateDilate {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (f : 𝓢((Fin d → ℝ), ℂ)) : 𝓢((Fin d → ℝ), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ (Fin d → ℝ) L⁻¹ (inv_ne_zero hL)).toContinuousLinearEquiv f

@[simp] theorem schwartzCoordinateDilate_apply {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (f : 𝓢((Fin d → ℝ), ℂ)) (x : Fin d → ℝ) :
    schwartzCoordinateDilate hL f x = f (L⁻¹ • x) := rfl

/-- TARGET L1035, L1541, L1575: Poisson summation on `L⁻¹ℤ^d`.
The amplitude need not be a product. -/
theorem poisson_scaled_coordinates {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ))
    {L : ℝ} (hL : 0 < L) :
    (∑' n : Fin d → ℤ, f (fun i => (n i : ℝ) / L)) =
      (L ^ d : ℂ) * ∑' m : Fin d → ℤ, timeFourier f (fun i => L * (m i : ℝ)) := by
  have h := poisson_integer (schwartzCoordinateDilate hL.ne' f)
  simp only [schwartzCoordinateDilate_apply] at h
  have he : (schwartzCoordinateDilate hL.ne' f : (Fin d → ℝ) → ℂ) =
      fun x => f (L⁻¹ • x) := rfl
  rw [he] at h
  simp_rw [timeFourier_comp_inv_smul f hL] at h
  change (∑' n : Fin d → ℤ, f (fun i => L⁻¹ * (n i : ℝ))) =
    ∑' m : Fin d → ℤ, (L ^ d : ℝ) • timeFourier f (fun i => L * (m i : ℝ)) at h
  simpa only [div_eq_mul_inv, mul_comm _ L⁻¹, Complex.real_smul,
    Complex.ofReal_pow, tsum_mul_left] using h

/-- The compactly supported smooth form of TARGET's Poisson summation.
No separate Fourier decay or summability assumptions are required. -/
theorem poisson_scaled_smooth_compact {d : ℕ} {f : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {L : ℝ} (hL : 0 < L) :
    (∑' n : Fin d → ℤ, f (fun i => (n i : ℝ) / L)) =
      (L ^ d : ℂ) * ∑' m : Fin d → ℤ, timeFourier f (fun i => L * (m i : ℝ)) :=
  poisson_scaled_coordinates (hc.toSchwartzMap hf) hL

end WaveTurbulence.Fourier
