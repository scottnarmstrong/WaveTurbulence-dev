/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalBoxKernel

/-!
# Joint measurability of the literal causal box amplitudes

All phase and interval parameters may depend measurably on the remaining
clocks. The hard indicators impose no differentiability requirement.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- A balanced or unbalanced real linear phase is measurable in all of its data. -/
theorem measurable_linearTimePhase_comp {Z : Type*} [MeasurableSpace Z] {r : ℕ}
    {phase v : Z → Fin r → ℝ} (hp : Measurable phase) (hv : Measurable v) :
    Measurable (fun z => Fourier.linearTimePhase (phase z) (v z)) := by
  have hs : Measurable (fun z => ∑ j, phase z j * v z j) := by
    apply Finset.measurable_sum
    intro j _
    exact (((measurable_pi_apply j).comp hp).mul ((measurable_pi_apply j).comp hv))
  exact Complex.continuous_exp.measurable.comp
    ((Complex.continuous_ofReal.measurable.comp hs).mul measurable_const)

/-- Strict clock ordering is a measurable function of the clocks. -/
theorem measurable_strictOrderingWeight (n : ℕ) : Measurable (strictOrderingWeight n) := by
  apply Finset.measurable_prod
  intro i _
  have hi : Measurable ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Ioi
  exact Complex.continuous_ofReal.measurable.comp (hi.comp
    ((measurable_pi_apply i.castSucc).sub (measurable_pi_apply i.succ)))

/-- Measurability of one localized hard interval with parameter-dependent endpoints. -/
theorem measurable_hardLocalizedInterval_comp {Z : Type*} [MeasurableSpace Z] {χ : ℝ → ℝ}
    (hχ : Measurable χ) {a b x : Z → ℝ} (ha : Measurable a) (hb : Measurable b) (hx : Measurable x) :
    Measurable (fun z => hardLocalizedInterval χ (a z) (b z) (x z)) := by
  have hs : MeasurableSet {z | a z < x z ∧ x z ≤ b z} :=
    (measurableSet_lt ha hx).inter (measurableSet_le hx hb)
  exact (hχ.comp hx).mul (Measurable.ite hs measurable_const measurable_const)

/-- The literal causal amplitude is measurable jointly in all of its data. -/
theorem measurable_causalBoxAmplitude_comp {Z : Type*} [MeasurableSpace Z] (m : ℕ)
    {χ : ℝ → ℝ} (hχ : Measurable χ) {phase a b v : Z → Fin (m + 2) → ℝ}
    (hp : Measurable phase) (ha : Measurable a) (hb : Measurable b) (hv : Measurable v) :
    Measurable (fun z => causalBoxAmplitude m χ (phase z) (a z) (b z) (v z)) := by
  have hf : Measurable (fun z => coordinateFactorProduct
      (fun j => hardLocalizedInterval χ (a z j) (b z j)) (v z)) := by
    apply Finset.measurable_prod
    intro j _
    exact Complex.continuous_ofReal.measurable.comp (measurable_hardLocalizedInterval_comp hχ
      ((measurable_pi_apply j).comp ha) ((measurable_pi_apply j).comp hb) ((measurable_pi_apply j).comp hv))
  exact (hf.mul (measurable_linearTimePhase_comp hp hv)).mul
    ((measurable_strictOrderingWeight (m + 1)).comp hv)

end WaveTurbulence.Incoh
