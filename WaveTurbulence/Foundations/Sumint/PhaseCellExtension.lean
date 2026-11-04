/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TimeCellRegularity
public import WaveTurbulence.Foundations.Sumint.WeightedSourceExtension

/-!
# Single-lattice-input ambient extensions for spatial recombination

The finite lattice cutoff expresses the full frequency-dependent
extension as a finite linear combination of these fixed integrable
functions. This justifies Fourier recombination without assuming gains.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- The actual common output modulation as a scalar function. -/
@[expose] noncomputable def sourceOutputModulation {d : ℕ} (D : SumintDatum d)
    (t : Fin 3 → ℝ) : ℂ :=
  Complex.exp ((Real.pi*(∑ v, D.param v)*t 0 : ℝ)*Complex.I)

/-- The source output modulation is continuous. -/
theorem continuous_sourceOutputModulation {d : ℕ} (D : SumintDatum d) :
    Continuous (sourceOutputModulation D) := by
  unfold sourceOutputModulation
  fun_prop

/-- The source output modulation has exactly unit norm. -/
theorem norm_sourceOutputModulation {d : ℕ} (D : SumintDatum d) (t : Fin 3 → ℝ) :
    ‖sourceOutputModulation D t‖ = 1 := by
  rw [sourceOutputModulation,← sourceModulationFrequency_char]
  exact Circle.norm_coe _

/-- The ambient extension of a single native lattice phase, without its input character. -/
@[expose] noncomputable def phaseCellExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : Fin 3 → ℝ) : ℂ :=
  sourceOutputModulation D t *
    timeCellExtension D hI N h (D.phase L γ δ η x r 0) (sourceTimeShear t)

/-- Each fixed-input phase extension is measurable everywhere in native output time. -/
theorem measurable_phaseCellExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) (h L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) :
    Measurable (phaseCellExtension D hI N h L γ δ η x r) := by
  have hs := (measurable_timeCellExtension D hI N h _
    (measurable_phase D L γ δ η x r 0)).comp sourceTimeShearEquiv.measurable
  exact (continuous_sourceOutputModulation D).measurable.mul hs

/-- Each fixed-input phase extension satisfies genuine ambient time integrability. -/
theorem integrable_phaseCellExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) (h L γ δ η : ℝ) (hη : η ≤ 1/3)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) :
    Integrable (phaseCellExtension D hI N h L γ δ η x r) := by
  have hi := integrable_timeCellExtension D hI N h _ (measurable_phase D L γ δ η x r 0)
    (fun j => integrableOn_phase_localDomain D L γ δ η hη x r 0 ((j:ℝ)*h) h)
  have hs := (integrable_sourceTimeShear_iff _).mpr hi
  exact hs.bdd_mul (continuous_sourceOutputModulation D).measurable.aestronglyMeasurable
    (ae_of_all _ (fun t => (norm_sourceOutputModulation D t).le))

end WaveTurbulence.Sumint
