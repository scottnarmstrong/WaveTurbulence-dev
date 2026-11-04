/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeSelectedSourceIntegral
public import WaveTurbulence.Foundations.Incoh.SelectedClockIntegral
public import WaveTurbulence.Foundations.Incoh.SelectedMixturePhase
public import WaveTurbulence.Foundations.Incoh.PhaseClockIntegrability

/-!
# Exact remaining-clock representation at each selected lattice phase

The source time-domain restriction and temporal phases are literal. Their
integrability is proved for every phase array, before applying Fubini.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The actual expanded tree source integral has exactly the declared ordered fibers. -/
theorem TreeClockFibers.integral_expandedClockArray {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) (t : Fin 2 → ℝ) :
    (∫ w in T.timeDomain ∩ R.causalRootCut t,
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) *
        ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) =
      ∫ u : Fin T.selection.coordinates.restCount → ℝ,
        (T.selection.coordinates.restBox Q).indicator
          (fun _ => T.selection.coordinates.remainingMixtureFactor L γ δ Q p u) u *
        T.remainingDomain.indicator (fun u =>
          ∫ v in orderedClockDomain (m + 2) (t 0) (t 1) ∩ causalIntervalFiber m (T.lower u) (T.upper u),
            Fourier.linearTimePhase
              (T.selection.phase (fun i => linkTemporalFrequency L γ δ (Q i) (p i))) v) u := by
  let A := T.timeDomain ∩ R.causalRootCut t
  let phase := T.selection.phase (fun i => linkTemporalFrequency L γ δ (Q i) (p i))
  let H : (Fin (m + 2) → ℝ) × (Fin T.selection.coordinates.restCount → ℝ) → ℂ := fun z =>
    A.indicator (fun w => Fourier.linearTimePhase phase (T.selection.coordinates.equiv w).1)
      (T.selection.coordinates.equiv.symm z)
  have hA : MeasurableSet A := T.measurableSet_timeDomain.inter (R.measurableSet_causalRootCut t)
  have he (w : Fin n → Fin 2 → ℝ) :
      A.indicator (fun w =>
        (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) *
        ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) w =
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) *
        H (T.selection.coordinates.equiv w) := by
    have hp := T.selection.prod_linkMixturePhase L γ δ Q p
      (T.selection.coordinates.equiv w).1 (T.selection.coordinates.equiv w).2
    simp only [Prod.eta, MeasurableEquiv.symm_apply_apply] at hp
    by_cases hw : w ∈ A <;> simp [H, hw, hp, phase]
  have hi := integrable_expandedLinkClockArray hL γ δ Q T.selection.coordinates.rootLinks p hA
  have hi' := hi.congr (Filter.Eventually.of_forall he)
  rw [← integral_indicator hA]
  simp_rw [he]
  rw [T.selection.coordinates.integral_selectedClockAmplitude L γ δ Q p H hi']
  apply integral_congr_ae
  filter_upwards [] with u
  dsimp only [H, A]
  rw [T.integral_selectedSourcePhase R hfirst hlast phase u t]

end WaveTurbulence.Incoh
