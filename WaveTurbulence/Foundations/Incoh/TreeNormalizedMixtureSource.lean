/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeCausalMixtureSource
public import WaveTurbulence.Foundations.Incoh.NormalizedLinkMixture
public import WaveTurbulence.Foundations.Incoh.CausalOrderingZero

/-!
# Source normalization of the literal causal phase mixture

The coupling is the exact source coupling, including its factor of two.
External cutoffs remain present on the entire forward clock half-plane.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- The literal normalized phase kernel for the structural tree clock fibers. -/
@[expose] def TreeClockFibers.causalPhaseKernel {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (χ : ℝ → ℝ) (L γ δ : ℝ) (t : Fin 2 → ℝ) : ℂ :=
  ∫ z, normalizedLinkMixtureAmplitude L γ δ Q T.selection.coordinates.rootLinks T.mixtureDomain z *
    universalCausalBoxKernel m χ t (T.mixtureParameters L γ δ z)
    ∂productLinkMixtureMeasure d n T.selection.coordinates.rootLinks

/-- Exact source agreement with the full source coupling and both external cutoffs. -/
theorem TreeClockFibers.causalPhaseKernel_eq_source {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ} (hmχ : Measurable χ)
    (hc : Fourier.CutoffControl χ)
    (hχ : ∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1)
    {t : Fin 2 → ℝ} (hst : t 1 ≤ t 0) :
    T.causalPhaseKernel χ L γ δ t =
      (χ (t 0) : ℂ) * (χ (t 1) : ℂ) * R.causalKernel L γ δ Q T.timeDomain t := by
  unfold causalPhaseKernel
  simp_rw [normalizedLinkMixtureAmplitude, mul_assoc]
  rw [integral_const_mul, T.causalMixture_eq_source R hfirst hlast hL γ δ hmχ hc hχ hst]
  unfold RootCoordinates.causalKernel normalizedLinkIntegral
  ac_rfl

/-- All literal normalized causal phase mixtures vanish at reversed external clocks. -/
theorem TreeClockFibers.causalPhaseKernel_eq_zero_of_reverse {d n m : ℕ}
    {Q : Fin n → LayerLink d} (T : TreeClockFibers m Q) (χ : ℝ → ℝ) (L γ δ : ℝ)
    {t : Fin 2 → ℝ} (ht : t 0 ≤ t 1) : T.causalPhaseKernel χ L γ δ t = 0 := by
  unfold causalPhaseKernel universalCausalBoxKernel
  simp_rw [causalBoxKernel_eq_zero_of_reverse χ _ _ _ ht, mul_zero]
  exact integral_zero _ _

end WaveTurbulence.Incoh
