/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSliceEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ParametricHalfCell

/-! # Joint measurability of the actual source Wick slices -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT WithLp

/-- The actual lattice series is jointly measurable in source frequency
and all modulation parameters, without an almost-everywhere replacement. -/
theorem stronglyMeasurable_normalizedWickSlice_joint {d n : ℕ}
    (L δ γ : ℝ) (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (J : Finset (Fin n)) {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      normalizedWickSlice L δ γ σ z p.2.1 p.2.2 J C p.1) := by
  unfold normalizedWickSlice
  apply stronglyMeasurable_const.mul
  apply Measurable.stronglyMeasurable
  apply Measurable.tsum
  intro θ
  apply measurable_const.mul
  apply Measurable.mul
  · unfold halfCellAmplitude
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro j _
      have hc : Continuous (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
          Real.fourierChar (inner ℝ (p.2.1 j) (latticePoint L (θ j).1))) := by fun_prop
      exact (hc.smul continuous_const).measurable
    · apply Finset.measurable_prod
      intro j _
      have hc : Continuous (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
          Real.fourierChar (inner ℝ (p.2.2 j) (latticePoint L (θ j).2))) := by fun_prop
      exact (hc.smul continuous_const).measurable
  · unfold resProfile
    apply measurable_const.mul
    exact (hC.comp_measurable
      (g := fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
        ((fun j : {j : Fin n // j ∉ J} => wickLatticeEnergy L (L^(2*γ)*δ) θ j.val),p.1))
      (measurable_const.prodMk measurable_fst)).measurable

end WaveTurbulence.RegAsymp
