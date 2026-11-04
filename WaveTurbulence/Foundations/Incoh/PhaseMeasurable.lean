/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.OrderedIntegralMeasurable
public import WaveTurbulence.Foundations.Fourier.BalancedAmplitude
public import WaveTurbulence.Foundations.Fourier.WeightedOrderedIntegral

/-!
# Measurable phase amplitudes and cutoff ordered kernels

Arbitrary measurable dependence on internal clocks is compatible with
literal ordered integration and the universal phase envelope.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Joint measurable dependence of the balanced phase amplitude. -/
theorem measurable_balancedCutoffAmplitude {Z : Type*} [MeasurableSpace Z] {m : ℕ}
    {χ : ℝ → ℝ} (hχ : Measurable χ) {phase : Z → Fin m → ℝ} (hp : Measurable phase)
    {F : Z × (Fin 2 → ℝ) → ℂ} (hF : Measurable F) (i j : Fin m) :
    Measurable (fun z : Z × (Fin m → ℝ) => Fourier.balancedCutoffAmplitude χ (phase z.1)
      (fun u => F (z.1, u)) i j z.2) := by
  have hc : Measurable (fun z : Z × (Fin m → ℝ) => Fourier.coordinateCutoff χ z.2) := by
    unfold Fourier.coordinateCutoff
    apply Finset.measurable_prod
    intro k _
    exact Complex.continuous_ofReal.measurable.comp
      (hχ.comp ((measurable_pi_apply k).comp measurable_snd))
  have hs : Measurable (fun z : Z × (Fin m → ℝ) => ∑ k, phase z.1 k * z.2 k) := by
    apply Finset.measurable_sum
    intro k _
    exact (((measurable_pi_apply k).comp hp).comp measurable_fst).mul
      ((measurable_pi_apply k).comp measurable_snd)
  have he : Measurable (fun z : Z × (Fin m → ℝ) => Fourier.linearTimePhase (phase z.1) z.2) :=
    Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp hs).mul measurable_const)
  apply (hc.mul he).mul
  apply hF.comp
  apply measurable_fst.prodMk
  apply Measurable.of_eval
  intro k
  fin_cases k
  · exact (measurable_pi_apply i).comp measurable_snd
  · exact (measurable_pi_apply j).comp measurable_snd

/-- Measurable amplitudes and output clocks give measurable cutoff ordered kernels. -/
theorem stronglyMeasurable_weightedOrderedIntegral_comp {Z : Type*} [MeasurableSpace Z]
    {m : ℕ} {χ : ℝ → ℝ} (hχ : Measurable χ)
    {F : Z × (Fin m → ℝ) → ℂ} (hF : StronglyMeasurable F)
    {t : Z → Fin 2 → ℝ} (ht : Measurable t) :
    StronglyMeasurable (fun z => Fourier.weightedOrderedIntegral m χ χ (fun v => F (z, v)) (t z)) := by
  have hc (j : Fin 2) : StronglyMeasurable (fun z => (χ (t z j) : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (hχ.comp ((measurable_pi_apply j).comp ht))).stronglyMeasurable
  exact ((hc 0).mul (hc 1)).mul (stronglyMeasurable_orderedIntegral m hF
    ((measurable_pi_apply 1).comp ht) ((measurable_pi_apply 0).comp ht))

end WaveTurbulence.Incoh
