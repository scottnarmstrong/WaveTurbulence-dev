/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalAmplitudeSource
public import WaveTurbulence.Foundations.Incoh.OrderedIntegralSet

/-!
# The literal causal phase kernel integrates over the source clock fiber

The forward external-clock formula is an exact set-integral identity.
All interval and strict descendant constraints remain in the domain.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Interval fibers with strict adjacent ordering are Borel sets. -/
theorem measurableSet_causalIntervalFiber (m : ℕ) (a b : Fin (m + 2) → ℝ) :
    MeasurableSet (causalIntervalFiber m a b) := by
  change MeasurableSet ({v : Fin (m + 2) → ℝ | ∀ j, a j < v j ∧ v j ≤ b j} ∩
    {v : Fin (m + 2) → ℝ | ∀ j : Fin (m + 1), v j.succ < v j.castSucc})
  apply MeasurableSet.inter
  · rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_lt measurable_const (measurable_pi_apply j)).inter
      (measurableSet_le (measurable_pi_apply j) measurable_const)
  · rw [ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_lt (measurable_pi_apply j.succ)
      (measurable_pi_apply j.castSucc)

/-- TARGET (incohproof22)–(23), exact selected-clock source-domain formula. -/
theorem causalBoxKernel_eq_sourceIntegral (m : ℕ) (χ : ℝ → ℝ)
    (phase a b : Fin (m + 2) → ℝ)
    (hχ : ∀ v : Fin (m + 2) → ℝ, (∀ j, a j < v j ∧ v j ≤ b j) → ∀ j, χ (v j) = 1)
    {t : Fin 2 → ℝ} (hst : t 1 ≤ t 0) :
    causalBoxKernel m χ phase a b t =
      (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
        ∫ v in orderedClockDomain (m + 2) (t 0) (t 1) ∩ causalIntervalFiber m a b,
          Fourier.linearTimePhase phase v := by
  have hs := measurableSet_causalIntervalFiber m a b
  have hm : StronglyMeasurable
      ((causalIntervalFiber m a b).indicator (Fourier.linearTimePhase phase)) :=
    (Fourier.linearTimePhase_contDiff phase).continuous.stronglyMeasurable.indicator hs
  have hb (v : Fin (m + 2) → ℝ) :
      ‖(causalIntervalFiber m a b).indicator (Fourier.linearTimePhase phase) v‖ ≤ 1 := by
    by_cases hv : v ∈ causalIntervalFiber m a b <;> simp [hv]
  have he : causalBoxAmplitude m χ phase a b =
      (causalIntervalFiber m a b).indicator (Fourier.linearTimePhase phase) :=
    funext (causalBoxAmplitude_eq_sourceIndicator m χ phase a b hχ)
  rw [causalBoxKernel, Fourier.weightedOrderedIntegral, he,
    orderedIntegral_eq_setIntegral (m + 2) hm hb hst, setIntegral_indicator hs]

end WaveTurbulence.Incoh
