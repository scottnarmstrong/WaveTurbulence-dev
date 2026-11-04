/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeSourcePhaseFibers
public import WaveTurbulence.Foundations.Incoh.TreeCausalMixtureIntegral

/-!
# The actual causal phase mixture equals the literal tree source integral

All mixture and Fubini integrability obligations follow from the actual
link factors and common causal kernel bound.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The actual positive-norm mixture agrees with the source on forward external clocks. -/
theorem TreeClockFibers.causalMixture_eq_source {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ} (hmχ : Measurable χ)
    (hc : Fourier.CutoffControl χ)
    (hχ : ∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1)
    {t : Fin 2 → ℝ} (hst : t 1 ≤ t 0) :
    (∫ z, productLinkMixtureAmplitude L γ δ Q T.selection.coordinates.rootLinks T.mixtureDomain z *
      universalCausalBoxKernel m χ t (T.mixtureParameters L γ δ z)
      ∂productLinkMixtureMeasure d n T.selection.coordinates.rootLinks) =
      (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
        ∫ w in T.timeDomain ∩ R.causalRootCut t, ∏ i, linkTimeFactor L γ δ (Q i) (w i) := by
  change (∫ z, T.causalMixtureIntegrand L γ δ χ t z
    ∂productLinkMixtureMeasure d n T.selection.coordinates.rootLinks) = _
  rw [T.integral_causalMixture_eq_remaining hL γ δ hmχ hc t,
    T.integral_source_eq_phaseFibers R hfirst hlast hL γ δ t, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ T.remainingDomain
  · have hχu (v : Fin (m + 2) → ℝ) (hv : ∀ j, T.lower u j < v j ∧ v j ≤ T.upper u j) :
        ∀ j, χ (v j) = 1 := hχ v (T.interval_mem_box u hu v hv)
    dsimp only [TreeClockFibers.remainingCausalKernel]
    rw [indicator_of_mem hu, indicator_of_mem hu]
    change _ * causalBoxKernel m χ
      (T.selection.phase (fun i => linkTemporalFrequency L γ δ (Q i) (p i)))
      (T.lower u) (T.upper u) t = _
    rw [causalBoxKernel_eq_sourceIntegral m χ _ _ _ hχu hst]
    ac_rfl
  · simp [TreeClockFibers.remainingCausalKernel, hu]

end WaveTurbulence.Incoh
