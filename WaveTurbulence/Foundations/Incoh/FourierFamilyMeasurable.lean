/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FourierMixture

/-!
# Joint measurability of parameterized time Fourier transforms

The parameter type needs only a measurable space. The statement does not
require time integrability because the Bochner integral has its usual total definition.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- A jointly measurable family has jointly measurable literal time Fourier transforms. -/
theorem stronglyMeasurable_timeFourier_family {r : ℕ} {U : Type*} [MeasurableSpace U]
    {K : (Fin r → ℝ) → U → ℂ}
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × U => K z.1 z.2)) :
    StronglyMeasurable (fun z : (Fin r → ℝ) × U => Fourier.timeFourier (fun t => K t z.2) z.1) := by
  let P : (((Fin r → ℝ) × U) × (Fin r → ℝ)) → ℂ :=
    fun z => Real.fourierChar (-Fourier.timePairing r z.2 z.1.1)
  have hP : Measurable P := by
    apply continuous_subtype_val.measurable.comp
    apply Real.continuous_fourierChar.measurable.comp
    change Measurable (fun z : (((Fin r → ℝ) × U) × (Fin r → ℝ)) => -(∑ j, z.2 j * z.1.1 j))
    apply Measurable.neg
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp measurable_snd).mul
      ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
  have hA : StronglyMeasurable (fun z : (((Fin r → ℝ) × U) × (Fin r → ℝ)) =>
      P z * K z.2 z.1.2) :=
    hP.stronglyMeasurable.mul (hK.comp_measurable
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hA.integral_prod_right' (ν := (volume : Measure (Fin r → ℝ)))

end WaveTurbulence.Incoh
