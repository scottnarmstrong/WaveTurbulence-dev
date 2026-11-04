/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CutoffPointwiseL1
public import WaveTurbulence.Foundations.Incoh.CoupleExtension

/-! # Pointwise physical bound of the actual canonical couple extension -/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The actual canonical couple extension is pointwise bounded by its physical root mass. -/
theorem RootCoordinates.enorm_coupleExtension_le {d n : ℕ} (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i))) (t : Fin 2 → ℝ) :
    ‖R.coupleExtension χ L γ δ Q I t‖ₑ ≤ ENNReal.ofReal hc.bound ^ 4 *
      eLpNorm (R.linkDensity L γ δ Q I) 1 := by
  have hb := enorm_cutoffDoubleIntegral_le hχ hc
    (R.integrable_localLinkDensity hL γ δ Q hI hbox) (t - R.baseRootTimes Q)
  rw [R.eLpNorm_localLinkDensity hL γ δ Q hI hbox 1] at hb
  exact hb

end WaveTurbulence.Incoh
