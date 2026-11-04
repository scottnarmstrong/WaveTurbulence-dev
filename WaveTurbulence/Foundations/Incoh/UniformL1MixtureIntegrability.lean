/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.DominatedFourierMixture

/-!
# Joint integrability from an actual uniform physical L¹ bound

This conditional transport lemma discharges the Fubini typing obligation
from measurable spectral amplitudes and physical kernel L¹ control.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- A finite physical L¹ envelope makes the amplitude-weighted family jointly integrable. -/
theorem integrable_amplitude_mul_family_of_uniformL1 {r : ℕ} {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (A : U → ℂ) (hA : StronglyMeasurable A) (hiA : Integrable A μ)
    (K : (Fin r → ℝ) → U → ℂ)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × U => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    {M : ℝ≥0∞} (hM : M < ⊤) (hb : ∀ u, eLpNorm (fun t => K t u) 1 ≤ M) :
    Integrable (fun z : (Fin r → ℝ) × U => A z.2 * K z.1 z.2) (volume.prod μ) := by
  have hm : StronglyMeasurable (fun z : (Fin r → ℝ) × U => A z.2 * K z.1 z.2) :=
    (hA.comp_measurable measurable_snd).mul hK
  refine ⟨hm.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  rw [lintegral_prod _ hm.enorm.aemeasurable,
    lintegral_lintegral_swap hm.enorm.aemeasurable]
  have hinner (u : U) : (∫⁻ t : Fin r → ℝ, ‖A u * K t u‖ₑ) ≤ ‖A u‖ₑ * M := by
    simp only [enorm_mul]
    have hKu : Measurable (fun t : Fin r → ℝ => ‖K t u‖ₑ) :=
      (hK.comp_measurable (g := fun t : Fin r → ℝ => (t, u))
        (measurable_id.prodMk measurable_const)).measurable.enorm
    rw [lintegral_const_mul _ hKu]
    apply mul_le_mul' le_rfl
    rw [← eLpNorm_one_eq_lintegral_enorm (hiK u).aestronglyMeasurable]
    exact hb u
  apply (lintegral_mono hinner).trans_lt
  rw [lintegral_mul_const _ hA.measurable.enorm]
  exact ENNReal.mul_lt_top (hasFiniteIntegral_iff_enorm.mp hiA.hasFiniteIntegral) hM

end WaveTurbulence.Incoh
