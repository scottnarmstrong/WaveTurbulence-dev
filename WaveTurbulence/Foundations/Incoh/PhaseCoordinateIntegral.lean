/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LinkMixture
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integrating the selected lattice phases recovers the literal link factors

The counting/Dirac measures match the mixture carrier exactly. Finite
support verifies counting-measure integrability before any sum/integral exchange.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- The lattice-coordinate measure used by a selected or unselected link. -/
@[expose] def phaseCoordinateMeasure (d : ℕ) (selected : Bool) :
    Measure ((Fin d → ℤ) × (Fin d → ℤ)) := if selected then Measure.count else Measure.dirac 0

instance sigmaFinite_phaseCoordinateMeasure (d : ℕ) (selected : Bool) :
    SigmaFinite (phaseCoordinateMeasure d selected) := by
  cases selected <;> unfold phaseCoordinateMeasure <;> simp only [Bool.false_eq_true, reduceIte, ite_true] <;>
    infer_instance

/-- A single term of the literal selected-link phase expansion. -/
@[expose] def phaseCoordinateTerm {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d) (selected : Bool)
    (t : Fin 2 → ℝ) (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  if selected then linkPhaseCoefficient L Q p *
    Complex.exp ((linkTemporalFrequency L γ δ Q p * (t 0 - t 1) : ℝ) * Complex.I) else 1

/-- The literal selected phase terms are integrable for counting measure. -/
theorem integrable_phaseCoordinateTerm {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (selected : Bool) (t : Fin 2 → ℝ) :
    Integrable (phaseCoordinateTerm L γ δ Q selected t) (phaseCoordinateMeasure d selected) := by
  cases selected
  · change Integrable (fun _ => (1 : ℂ)) (Measure.dirac (0 : (Fin d → ℤ) × (Fin d → ℤ)))
    exact integrable_const _
  · apply integrable_count_iff.mpr
    simpa only [phaseCoordinateTerm, ite_true, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
      (integrable_count_iff.mp (integrable_linkPhaseCoefficient hL Q))

/-- Integrating one selected coordinate yields exactly the source link sum. -/
theorem integral_phaseCoordinateTerm {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (selected : Bool) (t : Fin 2 → ℝ) :
    (∫ p, phaseCoordinateTerm L γ δ Q selected t p ∂phaseCoordinateMeasure d selected) =
      if selected then linkTimeFactor L γ δ Q t else 1 := by
  cases selected
  · change (∫ _p : (Fin d → ℤ) × (Fin d → ℤ), (1 : ℂ) ∂Measure.dirac 0) = 1
    rw [integral_dirac]
  · have hi := integrable_phaseCoordinateTerm hL γ δ Q true t
    change Integrable (phaseCoordinateTerm L γ δ Q true t) Measure.count at hi
    rw [show phaseCoordinateMeasure d true = Measure.count from rfl, integral_countable hi]
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul, ite_true]
    exact (linkTimeFactor_eq_phase_sum L γ δ Q t).symm

end WaveTurbulence.Incoh
