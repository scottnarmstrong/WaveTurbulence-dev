/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalAmplitudeMeasurable
public import WaveTurbulence.Foundations.Incoh.CausalBoxData
public import WaveTurbulence.Foundations.Incoh.PhaseMeasurable

/-!
# Joint measurability of the universal causal selected-clock kernels

The proof uses the actual hard amplitudes and measurable ordered
integration. No extra regularity is imposed on the internal-clock data.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- The causal kernel is measurable in arbitrary measurable phase/interval parameters. -/
theorem stronglyMeasurable_causalBoxKernel_family {P : Type*} [MeasurableSpace P]
    (m : ℕ) {χ : ℝ → ℝ} (hχ : Measurable χ)
    {phase a b : P → Fin (m + 2) → ℝ} (hp : Measurable phase) (ha : Measurable a) (hb : Measurable b) :
    StronglyMeasurable (fun z : (Fin 2 → ℝ) × P => causalBoxKernel m χ (phase z.2) (a z.2) (b z.2) z.1) := by
  have hA : Measurable (fun z : P × (Fin (m + 2) → ℝ) =>
      causalBoxAmplitude m χ (phase z.1) (a z.1) (b z.1) z.2) :=
    measurable_causalBoxAmplitude_comp m hχ (hp.comp measurable_fst) (ha.comp measurable_fst)
      (hb.comp measurable_fst) measurable_snd
  apply stronglyMeasurable_weightedOrderedIntegral_comp hχ
    (F := fun z : ((Fin 2 → ℝ) × P) × (Fin (m + 2) → ℝ) =>
      causalBoxAmplitude m χ (phase z.1.2) (a z.1.2) (b z.1.2) z.2) ?_ measurable_fst
  exact (hA.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable

/-- All structural data are covered by one jointly measurable universal kernel. -/
theorem stronglyMeasurable_universalCausalBoxKernel (m : ℕ) {χ : ℝ → ℝ} (hχ : Measurable χ) :
    StronglyMeasurable (fun z : (Fin 2 → ℝ) × CausalBoxData m => universalCausalBoxKernel m χ z.1 z.2) :=
  stronglyMeasurable_causalBoxKernel_family m hχ (CausalBoxData.measurable_phase m)
    (CausalBoxData.measurable_lower m) (CausalBoxData.measurable_upper m)

end WaveTurbulence.Incoh
