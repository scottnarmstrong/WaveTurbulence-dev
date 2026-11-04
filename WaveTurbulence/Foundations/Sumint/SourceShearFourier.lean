/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceFrequencyShear
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Exact Fourier change of variables under the source shear

Both identities retain the native Lebesgue measure and hold for all
inputs, with the usual Bochner integral convention.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- The source time shear preserves precisely the time integrability guard. -/
theorem integrable_sourceTimeShear_iff (f : (Fin 3 → ℝ) → ℂ) :
    Integrable (fun t => f (sourceTimeShear t)) ↔ Integrable f :=
  measurePreserving_sourceTimeShear.integrable_comp_emb sourceTimeShearEquiv.measurableEmbedding

/-- The Fourier transform of a source time shear is the inverse-transposed frequency shear. -/
theorem timeFourier_sourceTimeShear (f : (Fin 3 → ℝ) → ℂ) (ξ : Fin 3 → ℝ) :
    Fourier.timeFourier (fun t => f (sourceTimeShear t)) ξ =
      Fourier.timeFourier f (sourceFrequencyShear ξ) := by
  have hi := (measurePreserving_sourceTimeShear.symm sourceTimeShearEquiv).integral_comp
    sourceTimeShearEquiv.symm.measurableEmbedding
    (fun t => (Real.fourierChar (-Fourier.timePairing 3 t ξ):ℂ)*f (sourceTimeShear t))
  change (∫ z, (Real.fourierChar (-Fourier.timePairing 3 (sourceTimeUnshear z) ξ):ℂ)*
    f (sourceTimeShear (sourceTimeUnshear z))) =
    ∫ t, (Real.fourierChar (-Fourier.timePairing 3 t ξ):ℂ)*f (sourceTimeShear t) at hi
  simp_rw [sourceTimeShear_unshear,timePairing_unshear] at hi
  exact hi.symm

end WaveTurbulence.Sumint
