/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourierEndpoints
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic

/-!
# Continuity of the Fourier pairing on `L¹ × L¹`

The ordinary Fourier pairing is a continuous bilinear form on two `L¹`
spaces. This lets simultaneous `L¹` and `Lᵖ` approximation carry the
finite-step Hausdorff–Young estimate to integrable `Lᵖ` functions.
-/

public section

open MeasureTheory
open scoped FourierTransform ENNReal BoundedContinuousFunction

namespace WaveTurbulence.Fourier

/-- Bounded continuous functions embed continuously in `L∞`, for any measure. -/
@[expose] noncomputable def boundedContinuousToLInfinity {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] (μ : Measure α) :
    (α →ᵇ ℂ) →L[ℂ] Lp ℂ ∞ μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (BoundedContinuousFunction.memLp_top (μ := μ) f).toLp f
      map_add' := fun f g => MemLp.toLp_add
        (BoundedContinuousFunction.memLp_top (μ := μ) f)
        (BoundedContinuousFunction.memLp_top (μ := μ) g)
      map_smul' := fun c f => MemLp.toLp_const_smul c
        (BoundedContinuousFunction.memLp_top (μ := μ) f) }
    1 (fun f => by
      change ‖(BoundedContinuousFunction.memLp_top (μ := μ) f).toLp f‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_toLp]
      apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg f)
      rw [eLpNorm_exponent_top f.continuous.aestronglyMeasurable]
      exact eLpNormEssSup_le_of_ae_bound (ae_of_all _ fun x => f.norm_coe_le_norm x))

/-- The embedding into `L∞` preserves the original function almost everywhere. -/
theorem boundedContinuousToLInfinity_coeFn {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) (f : α →ᵇ ℂ) :
    (boundedContinuousToLInfinity μ f : α → ℂ) =ᵐ[μ] f :=
  (BoundedContinuousFunction.memLp_top (μ := μ) f).coeFn_toLp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The Fourier pairing as a continuous bilinear map on two `L¹` spaces. -/
@[expose] noncomputable def fourierL1Pairing :
    Lp (α := V) ℂ 1 (volume : Measure V) →L[ℂ]
      Lp (α := V) ℂ 1 (volume : Measure V) →L[ℂ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure V) ∞ 1).comp
    ((boundedContinuousToLInfinity (volume : Measure V)).comp (Real.Lp.fourierTransformCLM V ℂ))

/-- Agreement of the continuous pairing with the ordinary Fourier integral. -/
theorem fourierL1Pairing_toLp {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    fourierL1Pairing ((memLp_one_iff_integrable.mpr hf).toLp f)
      ((memLp_one_iff_integrable.mpr hg).toLp g) = ∫ ξ, 𝓕 f ξ * g ξ := by
  let u := (memLp_one_iff_integrable.mpr hf).toLp f
  let v := (memLp_one_iff_integrable.mpr hg).toLp g
  change (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume ∞ 1
    (boundedContinuousToLInfinity volume (Real.Lp.fourierTransform u)) v = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [boundedContinuousToLInfinity_coeFn volume (Real.Lp.fourierTransform u),
    (memLp_one_iff_integrable.mpr hg).coeFn_toLp] with ξ hξ hξ'
  rw [hξ, hξ']
  change 𝓕 (u : V → ℂ) ξ * g ξ = 𝓕 f ξ * g ξ
  rw [Real.fourier_congr_ae (memLp_one_iff_integrable.mpr hf).coeFn_toLp]

end WaveTurbulence.Fourier
