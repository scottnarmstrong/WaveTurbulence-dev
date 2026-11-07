/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.KernelEndpointEnorm
public import WaveTurbulence.Foundations.SumintPar.SourceExitFrequencyPairing

/-!
# Positive Fourier frequency integral of the explicit source kernel

The exact kernel endpoint representation and the native scalar pairings
bound its quarter-weight Fourier integral by the sum of genuine sparse
endpoint L2 masses. No bound for these masses is assumed here.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- The actual sparse endpoint L2 mass, with one coordinate when the two selected times coincide. -/
@[expose] noncomputable def sourceExitL2Mass {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (F : (D.S.TVar → ℝ) → ℂ) (c h : ℝ) (upper : Bool) (v : D.S.TVar) : ℝ≥0∞ :=
  if v = firstTime D hI then
    eLpNorm (fun s : ℝ => sourceExitTransform D hI upper (firstTime D hI) F c h 0 s) 2
  else eLpNorm (fun q : ℝ × ℝ => sourceExitTransform D hI upper v F c h q.1 q.2) 2

/-- The explicit source kernel's positive Fourier integral is bounded by its actual sparse endpoint L2 masses. -/
theorem lintegral_timeFourier_kernelExtension_quarter_le {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (hFm : Measurable F) (hFi : IntegrableOn F (localInputTimeDomain D c h)) :
    (∫⁻ ξ : Fin 3 → ℝ, Fourier.timeWeight ((1:ℝ)/4) ξ*‖Fourier.timeFourier (kernelExtension D hI c h F) ξ‖ₑ) ≤
      sourceExitKernelConstant*((∑ v, sourceExitL2Mass D hI F c h true v)+
        (∑ v, sourceExitL2Mass D hI F c h false v)) := by
  let K (ξ : Fin 3 → ℝ) := Fourier.timeWeight ((1:ℝ)/4) ξ*scalarPowerKernel 1 (ξ 0)*
    scalarPowerKernel 1 (ξ 1)*scalarPowerKernel 1 (ξ 2)
  let g (upper : Bool) (v : D.S.TVar) (ξ : Fin 3 → ℝ) :=
    K ξ*‖sourceExitTransform D hI upper v F c h (ξ 0) (ξ 1+ξ 2)‖ₑ
  have hK : Measurable K := (((Fourier.timeWeight_measurable ((1:ℝ)/4)).mul
    ((measurable_scalarPowerKernel 1).comp (measurable_pi_apply 0))).mul
    ((measurable_scalarPowerKernel 1).comp (measurable_pi_apply 1))).mul
    ((measurable_scalarPowerKernel 1).comp (measurable_pi_apply 2))
  have hmap : Measurable (fun ξ : Fin 3 → ℝ => (ξ 0,ξ 1+ξ 2)) := by fun_prop
  have hg (upper : Bool) (v : D.S.TVar) : Measurable (g upper v) :=
    hK.mul (((measurable_sourceExitTransform D hI upper v F hFm c h).comp hmap).enorm)
  have hb (upper : Bool) (v : D.S.TVar) : (∫⁻ ξ, g upper v ξ) ≤
      sourceExitKernelConstant*sourceExitL2Mass D hI F c h upper v :=
    lintegral_sourceExitTransform_quarter_le_L2 D hI F hFm c h upper v
  have hsum (upper : Bool) : Measurable (fun ξ => ∑ v, g upper v ξ) :=
    Finset.measurable_sum _ (fun v _ => hg upper v)
  calc
    _ ≤ ∫⁻ ξ, (∑ v, g true v ξ)+(∑ v, g false v ξ) := by
      apply lintegral_mono
      intro ξ
      have he := mul_le_mul' (le_rfl : Fourier.timeWeight ((1:ℝ)/4) ξ ≤ Fourier.timeWeight ((1:ℝ)/4) ξ)
        (enorm_timeFourier_kernelExtension_le_exit_transforms D hI c h F hFm hFi ξ)
      apply he.trans_eq
      dsimp only [g]
      rw [← Finset.mul_sum,← Finset.mul_sum,← mul_add]
      dsimp only [K]
      ring
    _ = (∑ v, ∫⁻ ξ, g true v ξ)+(∑ v, ∫⁻ ξ, g false v ξ) := by
      rw [lintegral_add_left (hsum true)]
      congr 1 <;> apply lintegral_finsetSum' <;> intro v _ <;> exact (hg _ v).aemeasurable
    _ ≤ (∑ v, sourceExitKernelConstant*sourceExitL2Mass D hI F c h true v)+
        (∑ v, sourceExitKernelConstant*sourceExitL2Mass D hI F c h false v) :=
      add_le_add (Finset.sum_le_sum (fun v _ => hb true v)) (Finset.sum_le_sum (fun v _ => hb false v))
    _ = _ := by rw [← Finset.mul_sum,← Finset.mul_sum,mul_add]

end WaveTurbulence.SumintPar
