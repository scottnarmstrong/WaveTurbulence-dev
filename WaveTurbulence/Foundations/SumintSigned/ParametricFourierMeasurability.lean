/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintSigned.FourierFubini

/-!
# Joint measurability of parameterized time Fourier transforms

This supplies the Tonelli hypothesis for integrating localized Fourier
coefficients while retaining the output supremum inside the frequency
integral.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintSigned

/-- A jointly measurable coefficient has a jointly measurable time Fourier transform. -/
theorem measurable_parametric_timeFourier {α : Type*} [MeasurableSpace α] {r : ℕ}
    (F : α → (Fin r → ℝ) → ℂ)
    (hF : Measurable (fun p : α × (Fin r → ℝ) => F p.1 p.2)) :
    Measurable (fun p : α × (Fin r → ℝ) => Fourier.timeFourier (F p.1) p.2) := by
  have hp : Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) =>
      (Real.fourierChar (-Fourier.timePairing r p.1 p.2) : ℂ)) := by
    simp_rw [Real.fourierChar_apply]
    unfold Fourier.timePairing
    change Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) =>
      Complex.exp ((2*Real.pi*(-∑ j, p.1 j*p.2 j) : ℝ)*Complex.I))
    fun_prop
  have hproj : Measurable (fun p : (α × (Fin r → ℝ)) × (Fin r → ℝ) => (p.2,p.1.2)) :=
    measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  have hχ := hp.measurable.comp hproj
  change Measurable (fun p : (α × (Fin r → ℝ)) × (Fin r → ℝ) =>
    (Real.fourierChar (-Fourier.timePairing r p.2 p.1.2) : ℂ)) at hχ
  have hprojF : Measurable (fun p : (α × (Fin r → ℝ)) × (Fin r → ℝ) => (p.1.1,p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hFc := hF.comp hprojF
  change Measurable (fun p : (α × (Fin r → ℝ)) × (Fin r → ℝ) => F p.1.1 p.2) at hFc
  have hm := (hχ.mul hFc).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Fin r → ℝ)))
  change StronglyMeasurable (fun p : α × (Fin r → ℝ) =>
    ∫ t : Fin r → ℝ, (Real.fourierChar (-Fourier.timePairing r t p.2) : ℂ) * F p.1 t) at hm
  change Measurable (fun p : α × (Fin r → ℝ) =>
    ∫ t : Fin r → ℝ, Real.fourierChar (-Fourier.timePairing r t p.2) • F p.1 t)
  simpa only [Circle.smul_def, smul_eq_mul] using hm.measurable

end WaveTurbulence.SumintSigned
