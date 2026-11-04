/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CutoffDoubleL1
public import WaveTurbulence.Foundations.Incoh.CoupleExtension

/-!
# Actual physical L¹ bound for the canonical couple extension

Local-clock translations preserve physical L¹. The landed bounded cutoff
operator controls the output by the literal root marginal, uniformly in
all spectral center and shift parameters.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The literal canonical couple extension is time-integrable. -/
theorem RootCoordinates.integrable_coupleExtension {d n : ℕ} (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i))) :
    Integrable (R.coupleExtension χ L γ δ Q I) := by
  have hF := R.integrable_localLinkDensity hL γ δ Q hI hbox
  have hG := integrable_cutoffDoubleIntegral hχ hc hF
  change Integrable (fun t => Fourier.cutoffDoubleIntegral χ
    (R.localLinkDensity L γ δ Q I) (t - R.baseRootTimes Q))
  simpa only [sub_eq_add_neg] using hG.comp_add_right (-R.baseRootTimes Q)

/-- A fixed cutoff-dependent factor controls the actual couple extension's physical L¹ norm. -/
theorem RootCoordinates.eLpNorm_coupleExtension_one_le {d n : ℕ} (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i))) :
    eLpNorm (R.coupleExtension χ L γ δ Q I) 1 ≤
      (Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound) *
        eLpNorm (R.linkDensity L γ δ Q I) 1 := by
  let F := R.localLinkDensity L γ δ Q I
  have hF : Integrable F := R.integrable_localLinkDensity hL γ δ Q hI hbox
  have hG := integrable_cutoffDoubleIntegral hχ hc hF
  have he : eLpNorm (R.coupleExtension χ L γ δ Q I) 1 =
      eLpNorm (Fourier.cutoffDoubleIntegral χ F) 1 := by
    change eLpNorm (fun t => Fourier.cutoffDoubleIntegral χ F (t - R.baseRootTimes Q)) 1 = _
    simpa only [Function.comp_def, sub_eq_add_neg] using
      eLpNorm_comp_measurePreserving hG.aestronglyMeasurable
        (measurePreserving_add_right volume (-R.baseRootTimes Q))
  rw [he]
  apply (eLpNorm_cutoffDoubleIntegral_one_le hχ hc hF).trans
  exact le_of_eq (congrArg (fun a =>
    (Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound) * a)
    (R.eLpNorm_localLinkDensity hL γ δ Q hI hbox 1))

end WaveTurbulence.Incoh
