/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ScalarFourierMass

/-!
# Product mass of smooth compact scalar cutoff factors

This is the landed one-time asymmetric Fourier product estimate at the
integer weight one, transferred to the ordinary scalar coordinates.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
open scoped ContDiff
namespace WaveTurbulence.SumintPar

/-- Products of two smooth compact scalar cutoffs cost at most twice the product of weighted masses. -/
theorem scalarFourierMass_mul_le {f g : ℝ → ℂ} (hfc : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    scalarFourierMass (fun t => f t*g t) ≤ 2*scalarFourierMass f*scalarFourierMass g := by
  have hfi : Integrable f := hfs.continuous.integrable_of_hasCompactSupport hfc
  have hgi : Integrable g := hgs.continuous.integrable_of_hasCompactSupport hgc
  have hfgc : HasCompactSupport (fun t => f t*g t) := hfc.mul_right
  have hfgs : ContDiff ℝ ∞ (fun t => f t*g t) := hfs.mul hgs
  have hfgi : Integrable (fun t => f t*g t) := hfgs.continuous.integrable_of_hasCompactSupport hfgc
  have hgl : Continuous (fun t : Fin 1 → ℝ => g (t 0)) := hgs.continuous.comp (continuous_apply 0)
  have hfn : Fourier.timeFourierNorm 1 (fun t : Fin 1 → ℝ => f (t 0)) < ⊤ := by
    rw [timeFourierNorm_scalar_lift f hfi]
    exact scalarFourierMass_lt_top_of_smooth_compact hfc hfs
  have hgn : Fourier.timeFourierNorm |(1:ℝ)| (fun t : Fin 1 → ℝ => g (t 0)) < ⊤ := by
    rw [abs_one,timeFourierNorm_scalar_lift g hgi]
    exact scalarFourierMass_lt_top_of_smooth_compact hgc hgs
  have hb := Fourier.timeFourierNorm_mul_asymmetric_le (1:ℝ) hgl hfn hgn
  simpa only [abs_one,Real.rpow_one,ENNReal.ofReal_ofNat,timeFourierNorm_scalar_lift _ hfgi,
    timeFourierNorm_scalar_lift f hfi,timeFourierNorm_scalar_lift g hgi] using hb

end WaveTurbulence.SumintPar
