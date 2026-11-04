/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MixedMixtureBound

/-!
# Verifying joint integrability of kernel mixtures

An integrable time dominator and an integrable internal amplitude supply
the Fubini hypothesis used by the mixed Fourier mixture bound.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- A common time bound verifies the joint Fubini premise for an actual mixture. -/
theorem integrable_joint_kernel_mixture {r : ℕ} {U W : Type*}
    [MeasurableSpace U] [MeasurableSpace W] (μ : Measure U) [SFinite μ]
    {K : (Fin r → ℝ) → W → ℂ}
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × W => K z.1 z.2))
    {B : (Fin r → ℝ) → ℝ} (hB : Integrable B) (hb : ∀ t w, ‖K t w‖ ≤ B t)
    {A : U → ℂ} (hA : Integrable A μ) (hmA : StronglyMeasurable A)
    {p : U → W} (hp : Measurable p) :
    Integrable (fun z : (Fin r → ℝ) × U => A z.2 * K z.1 (p z.2)) (volume.prod μ) := by
  have hm : StronglyMeasurable (fun z : (Fin r → ℝ) × U => A z.2 * K z.1 (p z.2)) :=
    (hmA.comp_measurable measurable_snd).mul
      (hK.comp_measurable (measurable_fst.prodMk (hp.comp measurable_snd)))
  apply (hB.mul_prod hA.norm).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    change ‖A z.2 * K z.1 (p z.2)‖ ≤ B z.1 * ‖A z.2‖
    rw [norm_mul, mul_comm ‖A z.2‖]
    exact mul_le_mul_of_nonneg_right (hb z.1 (p z.2)) (norm_nonneg _))

/-- The common time bound also verifies integrability of every individual kernel slice. -/
theorem integrable_kernel_slice_of_dominator {r : ℕ} {W : Type*} [MeasurableSpace W]
    {K : (Fin r → ℝ) → W → ℂ}
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × W => K z.1 z.2))
    {B : (Fin r → ℝ) → ℝ} (hB : Integrable B) (hb : ∀ t w, ‖K t w‖ ≤ B t) (w : W) :
    Integrable (fun t => K t w) :=
  hB.mono' (hK.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => hb t w))

end WaveTurbulence.Incoh
