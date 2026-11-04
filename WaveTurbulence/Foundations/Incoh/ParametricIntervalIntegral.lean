/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FourierFamilyMeasurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Measurable families of oriented interval integrals

Moving endpoints are encoded by measurable half-open interval indicators.
This handles literal cutoff integration operators without continuity or
integrability assumptions on the jointly measurable family.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Joint strong measurability is retained by integration between measurable endpoints. -/
theorem stronglyMeasurable_intervalIntegral_family {U : Type*} [MeasurableSpace U]
    (a b : U → ℝ) (ha : Measurable a) (hb : Measurable b)
    (f : U × ℝ → ℂ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun s => ∫ u in a s..b s, f (s, u)) := by
  let A : U × ℝ → ℂ := {z : U × ℝ | a z.1 < z.2 ∧ z.2 ≤ b z.1}.indicator f
  let B : U × ℝ → ℂ := {z : U × ℝ | b z.1 < z.2 ∧ z.2 ≤ a z.1}.indicator f
  have hA : StronglyMeasurable A := hf.indicator
    ((measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hb.comp measurable_fst)))
  have hB : StronglyMeasurable B := hf.indicator
    ((measurableSet_lt (hb.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (ha.comp measurable_fst)))
  have he (s : U) : (∫ u in a s..b s, f (s, u)) =
      (∫ u : ℝ, A (s, u)) - ∫ u : ℝ, B (s, u) := by
    rw [intervalIntegral]
    rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
    rfl
  simp_rw [he]
  exact (hA.integral_prod_right' (ν := volume)).sub (hB.integral_prod_right' (ν := volume))

end WaveTurbulence.Incoh
