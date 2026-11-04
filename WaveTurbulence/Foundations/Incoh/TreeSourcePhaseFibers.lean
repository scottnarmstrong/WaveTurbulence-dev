/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreePhaseClockIntegral
public import WaveTurbulence.Foundations.Incoh.ExpandedLinkIntegral

/-!
# The literal tree source integral as selected phases and remaining-clock fibers

Both lattice phase recovery and time-coordinate Fubini are exact. The
only time-domain assumptions are the structural tree fiber fields.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- TARGET (incohproof21)–(23), complete literal phase/fiber representation. -/
theorem TreeClockFibers.integral_source_eq_phaseFibers {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (t : Fin 2 → ℝ) :
    (∫ w in T.timeDomain ∩ R.causalRootCut t, ∏ i, linkTimeFactor L γ δ (Q i) (w i)) =
      ∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
        (∫ u : Fin T.selection.coordinates.restCount → ℝ,
          (T.selection.coordinates.restBox Q).indicator
            (fun _ => T.selection.coordinates.remainingMixtureFactor L γ δ Q p u) u *
          T.remainingDomain.indicator (fun u =>
            ∫ v in orderedClockDomain (m + 2) (t 0) (t 1) ∩ causalIntervalFiber m (T.lower u) (T.upper u),
              Fourier.linearTimePhase
                (T.selection.phase (fun i => linkTemporalFrequency L γ δ (Q i) (p i))) v) u)
        ∂Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ T.selection.coordinates.rootLinks))) := by
  let A := T.timeDomain ∩ R.causalRootCut t
  have hA : MeasurableSet A := T.measurableSet_timeDomain.inter (R.measurableSet_causalRootCut t)
  have hbox : A ⊆ univ.pi (fun i => linkBox (Q i)) :=
    fun _ hw => T.timeDomain_subset_linkBoxes hw.1
  have hm : Measurable (fun z : Fin n → LinkMixturePoint d => fun i => (z i).2) :=
    Measurable.of_eval (fun i => measurable_snd.comp (measurable_pi_apply i))
  rw [integral_source_eq_expandedMixture hL γ δ Q T.selection.coordinates.rootLinks hA hbox,
    integral_phaseTimeSplit_clocksFirst T.selection.coordinates.rootLinks _
      (integrable_expandedLinkMixture hL γ δ Q T.selection.coordinates.rootLinks (hA.preimage hm))]
  apply integral_congr_ae
  filter_upwards [] with p
  calc
    _ = ∫ w in A,
        (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) *
          ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i) := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      filter_upwards [] with w
      by_cases hw : w ∈ A <;> simp [productLinkMixtureAmplitude, hw]
    _ = _ := T.integral_expandedClockArray R hfirst hlast hL γ δ p t

end WaveTurbulence.Incoh
