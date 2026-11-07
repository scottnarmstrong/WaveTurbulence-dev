/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ScalarFourierScaling

/-!
# Exact nonnegative scalar dilation of Lebesgue measure

The positive scale h has Jacobian h. The formula also applies to
nonnegative Fourier mass functions without an integrability premise.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
namespace WaveTurbulence.SumintPar

/-- Scalar nonnegative integrals scale by the reciprocal positive dilation. -/
theorem lintegral_scalar_mul {h : ℝ} (hh : 0 < h) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ, f (h*x)) = ENNReal.ofReal h⁻¹*(∫⁻ x : ℝ, f x) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.smul (Units.mk0 h hh.ne')).toMeasurableEquiv
  have he := e.measurableEmbedding.lintegral_map f (μ := (volume : Measure ℝ))
  have hef : (e : ℝ → ℝ) = fun x => h*x := by funext x; rfl
  have hm : Measure.map e volume = ENNReal.ofReal h⁻¹ • (volume : Measure ℝ) := by
    have hs := Measure.map_addHaar_smul (volume : Measure ℝ) hh.ne'
    rw [hef]
    simpa only [Module.finrank_self,pow_one,abs_of_pos (inv_pos.mpr hh),smul_eq_mul] using hs
  rw [hm,lintegral_smul_measure] at he
  simpa only [hef,smul_eq_mul] using he.symm

end WaveTurbulence.SumintPar
