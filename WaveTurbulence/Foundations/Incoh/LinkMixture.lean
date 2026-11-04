/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LinkPhaseExpansion
public import WaveTurbulence.Foundations.Incoh.RootEnvelopeMass
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Actual selected-link mixture factors

Each selected link is expanded over its lattice phases; each unselected
link retains its full oscillatory time factor. Dummy phase coordinates
on unselected links carry a Dirac mass, not counting measure.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- One lattice phase coordinate and one pair of internal clocks. -/
abbrev LinkMixturePoint (d : ℕ) := ((Fin d → ℤ) × (Fin d → ℤ)) × (Fin 2 → ℝ)

/-- Count selected phases and fix unused phase coordinates to zero. -/
@[expose] def linkMixtureMeasure (d : ℕ) (selected : Bool) : Measure (LinkMixturePoint d) :=
  (if selected then (Measure.count : Measure ((Fin d → ℤ) × (Fin d → ℤ))) else Measure.dirac 0).prod volume

instance sigmaFinite_linkMixtureMeasure (d : ℕ) (selected : Bool) :
    SigmaFinite (linkMixtureMeasure d selected) := by
  cases selected <;> unfold linkMixtureMeasure <;> simp only [Bool.false_eq_true, reduceIte, ite_true] <;>
    infer_instance

/-- Literal factor in the phase/internal-clock mixture, including its actual unit layer box. -/
@[expose] def linkMixtureFactor {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d) (selected : Bool)
    (z : LinkMixturePoint d) : ℂ :=
  (linkBox Q).indicator
    (fun t => if selected then linkPhaseCoefficient L Q z.1 else linkTimeFactor L γ δ Q t) z.2

/-- Selected lattice coefficients are integrable for counting measure. -/
theorem integrable_linkPhaseCoefficient {d : ℕ} {L : ℝ} (hL : 0 < L) (Q : LayerLink d) :
    Integrable (linkPhaseCoefficient L Q) Measure.count :=
  integrable_count_iff.mpr (summable_norm_linkTerm hL 0 Q.toLinkParameters)

/-- The actual mixture factors are measurable, including their hard layer cutoffs. -/
theorem stronglyMeasurable_linkMixtureFactor {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (selected : Bool) :
    StronglyMeasurable (linkMixtureFactor L γ δ Q selected) := by
  have hp : Measurable (linkPhaseCoefficient L Q) := measurable_of_countable _
  have ht := (continuous_linkTimeFactor hL γ δ Q).measurable
  have hs : MeasurableSet {z : LinkMixturePoint d | z.2 ∈ linkBox Q} :=
    measurableSet_Icc.preimage measurable_snd
  cases selected
  · exact (ht.comp measurable_snd).stronglyMeasurable.indicator hs
  · exact (hp.comp measurable_fst).stronglyMeasurable.indicator hs

/-- Each factor is integrable against its literal phase/time measure. -/
theorem integrable_linkMixtureFactor {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (selected : Bool) :
    Integrable (linkMixtureFactor L γ δ Q selected) (linkMixtureMeasure d selected) := by
  have hbox : Integrable ((linkBox Q).indicator (fun _ => (1 : ℂ))) := by
    rw [integrable_indicator_iff (s := linkBox Q) measurableSet_Icc]
    exact integrableOn_const (by rw [volume_linkBox]; norm_num)
  have ht : Integrable ((linkBox Q).indicator (linkTimeFactor L γ δ Q)) :=
    (integrable_indicator_iff (s := linkBox Q) measurableSet_Icc).mpr (integrableOn_linkTimeFactor hL γ δ Q)
  cases selected
  · have h := (integrable_const (1 : ℂ) (μ := Measure.dirac (0 : (Fin d → ℤ) × (Fin d → ℤ)))).mul_prod ht
    change Integrable (fun z : LinkMixturePoint d =>
      (linkBox Q).indicator (linkTimeFactor L γ δ Q) z.2) ((Measure.dirac 0).prod volume)
    simpa only [one_mul] using h
  · have h := (integrable_linkPhaseCoefficient hL Q).mul_prod hbox
    change Integrable (fun z : LinkMixturePoint d =>
      (linkBox Q).indicator (fun _ => linkPhaseCoefficient L Q z.1) z.2) (Measure.count.prod volume)
    convert h using 1
    funext z
    by_cases hz : z.2 ∈ linkBox Q <;> simp [hz]

end WaveTurbulence.Incoh
