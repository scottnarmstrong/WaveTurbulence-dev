/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.NativeOneExitKernel
public import WaveTurbulence.Foundations.Sumint.NativeTwoExitKernel
public import WaveTurbulence.Foundations.Sumint.SourceSparseEndpointL2

/-!
# Actual sparse endpoint frequency pairings

One- and two-exit scalar estimates apply to the literal source endpoint
transform. The right side is its genuine frequency L2 norm, with the
coincident selected-time case handled in one dimension.
-/

public section
open MeasureTheory ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- A single absolute finite constant dominates both native exit kernel constants. -/
@[expose] noncomputable def sourceExitKernelConstant : ℝ≥0∞ :=
  nativeOneExitKernelConstant+nativeTwoExitKernelConstant

/-- The source exit kernel pairing constant is finite. -/
theorem sourceExitKernelConstant_lt_top : sourceExitKernelConstant < ⊤ :=
  ENNReal.add_lt_top.mpr ⟨nativeOneExitKernelConstant_lt_top,nativeTwoExitKernelConstant_lt_top⟩

/-- The literal source endpoint phase has a native quarter-weight frequency bound by its genuine L2 mass. -/
theorem lintegral_sourceExitTransform_quarter_le_L2 {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (F : (D.S.TVar → ℝ) → ℂ) (hF : Measurable F) (c h : ℝ) (upper : Bool) (v : D.S.TVar) :
    (∫⁻ ξ : Fin 3 → ℝ, Fourier.timeWeight ((1:ℝ)/4) ξ*scalarPowerKernel 1 (ξ 0)*
      scalarPowerKernel 1 (ξ 1)*scalarPowerKernel 1 (ξ 2)*
        ‖sourceExitTransform D hI upper v F c h (ξ 0) (ξ 1+ξ 2)‖ₑ) ≤
      sourceExitKernelConstant *
        (if v = firstTime D hI then
          eLpNorm (fun s : ℝ => sourceExitTransform D hI upper (firstTime D hI) F c h 0 s) 2
        else eLpNorm (fun q : ℝ × ℝ => sourceExitTransform D hI upper v F c h q.1 q.2) 2) := by
  by_cases hv : v = firstTime D hI
  · subst v
    rw [ite_eq_left rfl]
    let T (s : ℝ) := sourceExitTransform D hI upper (firstTime D hI) F c h 0 s
    have hmap : Measurable (fun s : ℝ => ((0:ℝ),s)) := measurable_const.prodMk measurable_id
    have hm : Measurable T := (measurable_sourceExitTransform D hI upper (firstTime D hI) F hF c h).comp hmap
    calc
      _ = ∫⁻ ξ : Fin 3 → ℝ, Fourier.timeWeight ((1:ℝ)/4) ξ*scalarPowerKernel 1 (ξ 0)*
          scalarPowerKernel 1 (ξ 1)*scalarPowerKernel 1 (ξ 2)*‖T (ξ 1+ξ 2-ξ 0)‖ₑ := by
        apply lintegral_congr
        intro ξ
        exact congrArg (fun z : ℂ => Fourier.timeWeight ((1:ℝ)/4) ξ*scalarPowerKernel 1 (ξ 0)*
          scalarPowerKernel 1 (ξ 1)*scalarPowerKernel 1 (ξ 2)*‖z‖ₑ)
          (sourceExitTransform_first_eq_difference D hI upper F c h (ξ 0) (ξ 1+ξ 2))
      _ ≤ nativeOneExitKernelConstant*(∫⁻ s : ℝ, ‖T s‖ₑ^(2:ℝ))^((1:ℝ)/2) :=
        lintegral_native_one_exit_quarter_le _ hm.enorm
      _ ≤ _ := by
        rw [frequency_lintegral_enorm_two_eq_eLpNorm hm.aestronglyMeasurable]
        exact mul_le_mul' (le_add_right le_rfl) le_rfl
  · rw [ite_eq_right hv]
    let T (q : ℝ × ℝ) := sourceExitTransform D hI upper v F c h q.1 q.2
    have hm : Measurable T := measurable_sourceExitTransform D hI upper v F hF c h
    calc
      _ ≤ nativeTwoExitKernelConstant*(∫⁻ q : ℝ × ℝ, ‖T q‖ₑ^(2:ℝ))^((1:ℝ)/2) :=
        lintegral_native_two_exit_quarter_le _ hm.enorm
      _ ≤ _ := by
        rw [frequency_lintegral_enorm_two_eq_eLpNorm hm.aestronglyMeasurable]
        exact mul_le_mul' (le_add_left le_rfl) le_rfl

end WaveTurbulence.Sumint
