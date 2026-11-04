/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.ParametricIntervalIntegral
public import WaveTurbulence.Foundations.Fourier.TimeIntegralOperators

/-!
# Joint measurability of the literal triangular cutoff operator

Both orientations use the source moving endpoints verbatim, without
assuming continuity or integrability of the measurable density family.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Actual causal cutoff integration preserves joint strong measurability. -/
theorem stronglyMeasurable_cutoffTriangleIntegral_family {U : Type*} [MeasurableSpace U]
    {χ : ℝ → ℝ} (hχ : Measurable χ) (F : (Fin 2 → ℝ) × U → ℂ)
    (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun z : (Fin 2 → ℝ) × U =>
      Fourier.cutoffTriangleIntegral χ (fun u => F (u, z.2)) z.1) := by
  have hc : Measurable (fun u : ℝ => (χ u : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hχ
  let G : (((Fin 2 → ℝ) × U) × ℝ) × ℝ → ℂ := fun z =>
    (χ z.1.2 : ℂ) * (χ z.2 : ℂ) * F (![z.1.2, z.2], z.1.1.2)
  have hG : StronglyMeasurable G :=
    ((hc.comp (measurable_snd.comp measurable_fst)).stronglyMeasurable.mul
      (hc.comp measurable_snd).stronglyMeasurable).mul
      (hF.comp_measurable (by fun_prop))
  have hv := stronglyMeasurable_intervalIntegral_family
    (fun s : ((Fin 2 → ℝ) × U) × ℝ => s.1.1 1)
    (fun s : ((Fin 2 → ℝ) × U) × ℝ => s.2)
    (by fun_prop) measurable_snd G hG
  have hu := stronglyMeasurable_intervalIntegral_family
    (fun s : (Fin 2 → ℝ) × U => s.1 1) (fun s : (Fin 2 → ℝ) × U => s.1 0)
    (by fun_prop) (by fun_prop)
    (fun s : ((Fin 2 → ℝ) × U) × ℝ => ∫ v in s.1.1 1..s.2, G (s, v)) hv
  exact (((hc.comp (by fun_prop : Measurable (fun z : (Fin 2 → ℝ) × U => z.1 0))).stronglyMeasurable.mul
    (hc.comp (by fun_prop : Measurable (fun z : (Fin 2 → ℝ) × U => z.1 1))).stronglyMeasurable).mul hu)

end WaveTurbulence.Incoh
