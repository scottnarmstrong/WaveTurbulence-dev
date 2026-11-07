/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ParametricFourierMeasurability
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Volume-preserving frequency coordinates for one and two exits

The sparse two-exit Fourier phase reflects its first frequency. The
one-exit phase uses the scalar frequency directly. Both coordinate
changes preserve the full L2 norm exactly.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
namespace WaveTurbulence.SumintPar

/-- Measurable coefficients have measurable coordinate time Fourier transforms. -/
theorem measurable_timeFourier_of_measurable {k : ℕ} (f : (Fin k → ℝ) → ℂ) (hf : Measurable f) :
    Measurable (Fourier.timeFourier f) := by
  have hphase : Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) =>
      (Real.fourierChar (-Fourier.timePairing k p.2 p.1):ℂ)) := by
    simp_rw [Real.fourierChar_apply]
    unfold Fourier.timePairing
    change Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) =>
      Complex.exp ((2*Real.pi*(-∑ j, p.2 j*p.1 j):ℝ)*Complex.I))
    fun_prop
  have hinput : Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => f p.2) := hf.comp measurable_snd
  have hm := (hphase.measurable.mul hinput).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Fin k → ℝ)))
  exact hm.measurable

/-- The reflected native two-exit frequency coordinates preserve product volume. -/
theorem measurePreserving_exitTwoFrequency :
    MeasurePreserving (fun q : ℝ × ℝ => (![-q.1,q.2] : Fin 2 → ℝ)) volume volume := by
  have hn : MeasurePreserving (fun q : ℝ × ℝ => (-q.1,q.2)) volume volume := by
    have hp := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (show MeasurePreserving (id : ℝ → ℝ) volume volume from ⟨measurable_id,Measure.map_id⟩)
    rw [Measure.volume_eq_prod]
    exact hp
  have hi := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := ℝ)) (volume_preserving_finTwoArrow ℝ)
  exact hi.comp hn

/-- The native single-exit scalar frequency coordinates preserve volume. -/
theorem measurePreserving_exitOneFrequency :
    MeasurePreserving (fun s : ℝ => (fun _ : Fin 1 => s)) volume volume :=
  MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ) (volume_preserving_funUnique (Fin 1) ℝ)

/-- The reflected two-exit frequency change preserves the Fourier L2 norm. -/
theorem eLpNorm_exitTwoFrequency {f : (Fin 2 → ℝ) → ℂ} (hf : Measurable f) :
    eLpNorm (fun q : ℝ × ℝ => f ![-q.1,q.2]) 2 = eLpNorm f 2 :=
  eLpNorm_comp_measurePreserving hf.aestronglyMeasurable measurePreserving_exitTwoFrequency

/-- The scalar single-exit frequency change preserves the Fourier L2 norm. -/
theorem eLpNorm_exitOneFrequency {f : (Fin 1 → ℝ) → ℂ} (hf : Measurable f) :
    eLpNorm (fun s : ℝ => f (fun _ => s)) 2 = eLpNorm f 2 :=
  eLpNorm_comp_measurePreserving hf.aestronglyMeasurable measurePreserving_exitOneFrequency

end WaveTurbulence.SumintPar
