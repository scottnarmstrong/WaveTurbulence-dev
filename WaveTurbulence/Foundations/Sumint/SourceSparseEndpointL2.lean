/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ExitFrequencyCoordinates
public import WaveTurbulence.Foundations.Sumint.SourceExitSelectedIdentity
public import WaveTurbulence.Foundations.Sumint.SourceExitTransformRegularity

/-!
# Exact L2 norms of actual sparse endpoint transforms

Reflection of the first two-exit frequency and scalar one-exit frequency
coordinates preserve volume. Thus the actual sparse transform has
exactly the established selected marginal Fourier L2 norm.
-/

public section
open MeasureTheory
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The actual two-exit sparse L2 norm equals its native selected Fourier L2 norm. -/
theorem eLpNorm_sourceExitTransform_two {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) (v : D.S.TVar) (hv : v ≠ firstTime D hI) :
    eLpNorm (fun q : ℝ × ℝ => sourceExitTransform D hI upper v (weightedCutoffInput D L γ δ η p ν r) c h q.1 q.2) 2 =
      eLpNorm (Fourier.timeFourier (selectedCoordinateMarginal ![v,firstTime D hI]
        (sourceExitSelectedTwo_injective D hI v hv) (sourceExitInput D hI L γ δ η p ν r c h upper v))) 2 := by
  simp_rw [sourceExitTransform_eq_selectedFourier_two D hI hL γ δ η hη p ν r c h upper v hv]
  apply eLpNorm_exitTwoFrequency
  exact measurable_timeFourier_of_measurable _ (measurable_selectedCoordinateMarginal _ _ _
    (measurable_sourceExitInput D hI hL γ δ η p ν r c h upper v))

/-- The actual coincident-exit sparse L2 norm equals its native one-coordinate Fourier L2 norm. -/
theorem eLpNorm_sourceExitTransform_one {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) :
    eLpNorm (fun s : ℝ => sourceExitTransform D hI upper (firstTime D hI)
      (weightedCutoffInput D L γ δ η p ν r) c h 0 s) 2 =
      eLpNorm (Fourier.timeFourier (selectedCoordinateMarginal (fun _ : Fin 1 => firstTime D hI)
        (fun _ _ _ => Subsingleton.elim _ _) (sourceExitInput D hI L γ δ η p ν r c h upper (firstTime D hI)))) 2 := by
  simp_rw [sourceExitTransform_eq_selectedFourier_one D hI hL γ δ η hη p ν r c h upper,sub_zero]
  apply eLpNorm_exitOneFrequency
  exact measurable_timeFourier_of_measurable _ (measurable_selectedCoordinateMarginal _ _ _
    (measurable_sourceExitInput D hI hL γ δ η p ν r c h upper (firstTime D hI)))

/-- The complex L2 norm is exactly the nonnegative frequency mass used in the endpoint kernel estimates. -/
theorem frequency_lintegral_enorm_two_eq_eLpNorm {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}
    {f : ι → ℂ} (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ^(2:ℝ) ∂μ)^((1:ℝ)/2) = eLpNorm f 2 μ := by
  symm
  simpa only [ENNReal.toReal_ofNat] using eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2:ENNReal) ≠ 0) (by norm_num : (2:ENNReal) ≠ ⊤) hf

end WaveTurbulence.Sumint
