/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.SelMix
public import WaveTurbulence.Foundations.Incoh.TreeSourcePhaseFibers

/-! # D5b-2 FILT-PROD: phase expansion and tree phase fibers (twins of `PhaseCoordinateIntegral`, `ExpandedLinkFactor`, `ExpandedLinkIntegral`, `PhaseClockIntegrability`, `TreePhaseClockIntegral`, `TreeSourcePhaseFibers`) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc
/-- A single term of the literal selected-link phase expansion. -/
def phaseCoordinateTermFilt {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) (selected : Bool)
    (t : Fin 2 → ℝ) (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  if selected then filtLinkPhaseCoefficient L Q φ p *
    Complex.exp ((linkTemporalFrequency L γ δ Q p * (t 0 - t 1) : ℝ) * Complex.I) else 1

/-- The literal selected phase terms are integrable for counting measure. -/
theorem integrable_phaseCoordinateTermFilt {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) (selected : Bool) (t : Fin 2 → ℝ) :
    Integrable (phaseCoordinateTermFilt L γ δ Q φ selected t) (phaseCoordinateMeasure d selected) := by
  cases selected
  · change Integrable (fun _ => (1 : ℂ)) (Measure.dirac (0 : (Fin d → ℤ) × (Fin d → ℤ)))
    exact integrable_const _
  · apply integrable_count_iff.mpr
    simpa only [phaseCoordinateTermFilt, ite_true, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
      (integrable_count_iff.mp (integrable_linkPhaseCoefficientFilt hL Q φ))

/-- Integrating one selected coordinate yields exactly the source link sum. -/
theorem integral_phaseCoordinateTermFilt {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) (selected : Bool) (t : Fin 2 → ℝ) :
    (∫ p, phaseCoordinateTermFilt L γ δ Q φ selected t p ∂phaseCoordinateMeasure d selected) =
      if selected then filtLinkTimeFactor L γ δ Q φ t else 1 := by
  cases selected
  · change (∫ _p : (Fin d → ℤ) × (Fin d → ℤ), (1 : ℂ) ∂Measure.dirac 0) = 1
    rw [integral_dirac]
  · have hi := integrable_phaseCoordinateTermFilt hL γ δ Q φ true t
    change Integrable (phaseCoordinateTermFilt L γ δ Q φ true t) Measure.count at hi
    rw [show phaseCoordinateMeasure d true = Measure.count from rfl, integral_countable hi]
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul, ite_true]
    exact (filtLinkTimeFactor_eq_phase_sum L γ δ Q φ t).symm

/-- The finite product phase integral recovers every selected oscillatory link at once. -/
theorem integral_phaseArray_termsFilt {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n)) (t : Fin n → Fin 2 → ℝ) :
    (∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
      ∏ i, phaseCoordinateTermFilt L γ δ (Q i) (φ i) (decide (i ∈ J)) (t i) (p i)
      ∂Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ J)))) =
      ∏ i, if i ∈ J then filtLinkTimeFactor L γ δ (Q i) (φ i) (t i) else 1 := by
  classical
  rw [integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_phaseCoordinateTermFilt hL γ δ (Q i) (φ i) (decide (i ∈ J)) (t i)]
  simp only [decide_eq_true_eq]

/-- Phase integration recovers the actual factor with its literal layer box. -/
theorem integral_expandedLinkFactorFilt {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : LayerLink d) (φ : ℝ → ℂ) (selected : Bool) (t : Fin 2 → ℝ) :
    (∫ p, linkMixtureFactorFilt L γ δ Q φ selected (p, t) *
      linkMixturePhase L γ δ Q selected (p, t) ∂phaseCoordinateMeasure d selected) =
      (linkBox Q).indicator (filtLinkTimeFactor L γ δ Q φ) t := by
  by_cases ht : t ∈ linkBox Q
  · simp only [linkMixtureFactorFilt, indicator_of_mem ht]
    cases selected
    · change (∫ _p, filtLinkTimeFactor L γ δ Q φ t * 1 ∂Measure.dirac 0) = _
      simp
    · change (∫ p, phaseCoordinateTermFilt L γ δ Q φ true t p ∂phaseCoordinateMeasure d true) = _
      rw [integral_phaseCoordinateTermFilt hL γ δ Q φ true t]
      simp
  · simp only [linkMixtureFactorFilt, indicator_of_notMem ht, zero_mul, integral_zero]

/-- Restoring all selected temporal phases preserves actual mixture integrability. -/
theorem integrable_expandedLinkMixtureFilt {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    Integrable (fun z => productLinkMixtureAmplitudeFilt L γ δ Q φ J S z *
      ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (z i))
      (productLinkMixtureMeasure d n J) := by
  have hm : Measurable (fun z : Fin n → LinkMixturePoint d =>
      ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (z i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (measurable_linkMixturePhase L γ δ (Q i) _).comp (measurable_pi_apply i)
  apply (integrable_productLinkMixtureAmplitudeFilt hL γ δ Q φ J hS).mul_bdd
    hm.stronglyMeasurable.aestronglyMeasurable (c := 1)
  exact Filter.Eventually.of_forall (fun z => by simp [norm_prod, norm_linkMixturePhase])



/-- Integrate all selected lattice phases while keeping the vertex clocks fixed. -/
theorem integral_expandedLinkArrayFilt {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n)) (t : Fin n → Fin 2 → ℝ) :
    (∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
      ∏ i, (linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ J)) (p i, t i) *
        linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (p i, t i))
      ∂Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ J)))) =
      ∏ i, (linkBox (Q i)).indicator (filtLinkTimeFactor L γ δ (Q i) (φ i)) (t i) := by
  classical
  rw [integral_fintype_prod_eq_prod (f := fun i p =>
    linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ J)) (p, t i) *
      linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (p, t i))]
  exact Finset.prod_congr rfl (fun i _ => integral_expandedLinkFactorFilt hL γ δ (Q i) (φ i) _ (t i))

/-- TARGET (incohproof21): the literal product integral equals its selected-phase mixture. -/
theorem integral_source_eq_expandedMixtureFilt {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n))
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    (∫ t in I, ∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)) =
      ∫ z, productLinkMixtureAmplitudeFilt L γ δ Q φ J
          ((fun z i => (z i).2) ⁻¹' I) z *
        ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (z i)
        ∂productLinkMixtureMeasure d n J := by
  classical
  have ht : Measurable (fun z : Fin n → LinkMixturePoint d => fun i => (z i).2) :=
    Measurable.of_eval (fun i => measurable_snd.comp (measurable_pi_apply i))
  rw [integral_phaseTimeSplit J _ (integrable_expandedLinkMixtureFilt hL γ δ Q φ J (hI.preimage ht)),
    ← integral_indicator hI]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hi : t ∈ I
  · have hib : ∀ i, t i ∈ linkBox (Q i) := fun i => hbox hi i (mem_univ i)
    simp only [productLinkMixtureAmplitudeFilt, mem_preimage, hi, indicator_of_mem]
    simp_rw [← Finset.prod_mul_distrib]
    rw [integral_expandedLinkArrayFilt hL γ δ Q φ J t]
    exact Finset.prod_congr rfl (fun i _ => (indicator_of_mem (hib i) _).symm)
  · simp [productLinkMixtureAmplitudeFilt, hi]



/-- Fixing any lattice phase leaves an integrable literal time factor. -/
theorem integrable_linkMixtureFactor_clockFilt {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) (selected : Bool)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    Integrable (fun t : Fin 2 → ℝ => linkMixtureFactorFilt L γ δ Q φ selected (p, t)) := by
  cases selected
  · exact (integrableOn_filtLinkTimeFactor hL γ δ Q φ).integrable_indicator
      (show MeasurableSet (linkBox Q) from measurableSet_Icc)
  · exact (show IntegrableOn (fun _ : Fin 2 → ℝ => filtLinkPhaseCoefficient L Q φ p) (linkBox Q) from
      continuous_const.integrableOn_Icc).integrable_indicator
        (show MeasurableSet (linkBox Q) from measurableSet_Icc)

/-- Any source-domain restriction of the literal expanded time integrand is integrable. -/
theorem integrable_expandedLinkClockArrayFilt {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n))
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    Integrable (I.indicator (fun t : Fin n → Fin 2 → ℝ =>
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ J)) (p i, t i)) *
        ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (p i, t i))) := by
  have hi : Integrable (fun t : Fin n → Fin 2 → ℝ =>
      ∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ J)) (p i, t i)) :=
    Integrable.fintype_prod_dep (fun i => integrable_linkMixtureFactor_clockFilt hL γ δ (Q i) (φ i) _ (p i))
  have hm : Measurable (fun t : Fin n → Fin 2 → ℝ =>
      ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (p i, t i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (measurable_linkMixturePhase L γ δ (Q i) _).comp
      (measurable_const.prodMk (measurable_pi_apply i))
  apply (hi.mul_bdd hm.stronglyMeasurable.aestronglyMeasurable (c := 1) ?_).indicator hI
  exact Filter.Eventually.of_forall (fun t => by simp [norm_prod, norm_linkMixturePhase])



/-- The actual expanded tree source integral has exactly the declared ordered fibers. -/
theorem TreeClockFibers.integral_expandedClockArrayFilt {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) (t : Fin 2 → ℝ) :
    (∫ w in T.timeDomain ∩ R.causalRootCut t,
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) *
        ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) =
      ∫ u : Fin T.selection.coordinates.restCount → ℝ,
        (T.selection.coordinates.restBox Q).indicator
          (fun _ => RootCoordinates.remainingMixtureFactorFilt T.selection.coordinates L γ δ Q φ p u) u *
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
        (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) *
        ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) w =
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) *
        H (T.selection.coordinates.equiv w) := by
    have hp := T.selection.prod_linkMixturePhase L γ δ Q p
      (T.selection.coordinates.equiv w).1 (T.selection.coordinates.equiv w).2
    simp only [Prod.eta, MeasurableEquiv.symm_apply_apply] at hp
    by_cases hw : w ∈ A <;> simp [H, hw, hp, phase]
  have hi := integrable_expandedLinkClockArrayFilt hL γ δ Q φ T.selection.coordinates.rootLinks p hA
  have hi' := hi.congr (Filter.Eventually.of_forall he)
  rw [← integral_indicator hA]
  simp_rw [he]
  rw [RootCoordinates.integral_selectedClockAmplitudeFilt T.selection.coordinates L γ δ Q φ p H hi']
  apply integral_congr_ae
  filter_upwards [] with u
  dsimp only [H, A]
  rw [T.integral_selectedSourcePhase R hfirst hlast phase u t]



/-- TARGET (incohproof21)–(23), complete literal phase/fiber representation. -/
theorem TreeClockFibers.integral_source_eq_phaseFibersFilt {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (t : Fin 2 → ℝ) :
    (∫ w in T.timeDomain ∩ R.causalRootCut t, ∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (w i)) =
      ∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
        (∫ u : Fin T.selection.coordinates.restCount → ℝ,
          (T.selection.coordinates.restBox Q).indicator
            (fun _ => RootCoordinates.remainingMixtureFactorFilt T.selection.coordinates L γ δ Q φ p u) u *
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
  rw [integral_source_eq_expandedMixtureFilt hL γ δ Q φ T.selection.coordinates.rootLinks hA hbox,
    integral_phaseTimeSplit_clocksFirst T.selection.coordinates.rootLinks _
      (integrable_expandedLinkMixtureFilt hL γ δ Q φ T.selection.coordinates.rootLinks (hA.preimage hm))]
  apply integral_congr_ae
  filter_upwards [] with p
  calc
    _ = ∫ w in A,
        (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i)) *
          ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (p i, w i) := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      filter_upwards [] with w
      by_cases hw : w ∈ A <;> simp [productLinkMixtureAmplitudeFilt, hw]
    _ = _ := TreeClockFibers.integral_expandedClockArrayFilt T φ R hfirst hlast hL γ δ p t


end WaveTurbulence.Flower.FiltProd
