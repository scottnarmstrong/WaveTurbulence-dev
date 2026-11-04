/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FrozenModulationMeasurable
public import WaveTurbulence.Foundations.Incoh.DominatedFourierMixture
public import WaveTurbulence.Foundations.Fourier.TimeProduct

/-!
# Fixed-clock traces in the mixed Fourier norm

TARGET's integer-endpoint variants of (incohproof23). A trace costs only
the fixed output cutoff and is uniform in the frozen value, even when that
value depends arbitrarily on the vector parameter.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- A cutoff trace of a smooth compact family preserves nonnegative Fourier regularity. -/
theorem mixedFourierNorm00_cutoffTimeTrace_le {r : ℕ} {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (F : (Fin r → ℝ) → V → ℂ) (hF : ∀ v, ContDiff ℝ ∞ (fun t => F t v))
    (hcF : ∀ v, HasCompactSupport (fun t => F t v)) (j : Fin r) (c : V → ℝ) :
    Fourier.mixedFourierNorm00 θ (fun t v => cutoffTimeTrace χ j (c v) (fun u => F u v) t) ≤
      (ENNReal.ofReal (2 ^ θ) * Fourier.timeFourierNorm θ (Fourier.coordinateCutoff (r := r) χ)) *
        Fourier.mixedFourierNorm00 θ F := by
  have hiF (v : V) : Integrable (fun t => F t v) :=
    (hF v).continuous.integrable_of_hasCompactSupport (hcF v)
  have hhF (v : V) : Integrable (Fourier.timeFourier (fun t => F t v)) :=
    Fourier.integrable_timeFourier_of_norm_lt_top (by norm_num : (0 : ℝ) ≤ 0)
      (Fourier.timeFourierNorm_lt_top_of_smooth_compact 0 (hcF v) (hF v))
  let A : V → (Fin r → ℝ) → ℂ := fun v ξ =>
    (Real.fourierChar (c v * ξ j) : ℂ) * Fourier.timeFourier (fun t => F t v) ξ
  have hcoe : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
  have hp (v : V) : Continuous (fun ξ : Fin r → ℝ => (Real.fourierChar (c v * ξ j) : ℂ)) :=
    hcoe.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hiA (v : V) : Integrable (A v) :=
    (hhF v).bdd_mul (hp v).aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      simp only [Circle.norm_coe]; exact le_rfl))
  have hmA (v : V) : StronglyMeasurable (A v) :=
    (hp v).stronglyMeasurable.mul (Fourier.timeFourier_continuous (hiF v)).stronglyMeasurable
  have hK := stronglyMeasurable_frozenModulation hχ j
  have hB := integrable_norm_coordinateCutoff (r := r) hχ hcχ
  have hb := fun t ξ => (norm_frozenModulation χ j t ξ).le
  have hj (v : V) := integrable_joint_kernel_mixture volume hK hB hb (hiA v) (hmA v) measurable_id
  have he (t : Fin r → ℝ) (v : V) : cutoffTimeTrace χ j (c v) (fun u => F u v) t =
      ∫ ξ, A v ξ * frozenModulation χ j t ξ :=
    cutoffTimeTrace_eq_fourier_mixture χ j (c v) (hiF v) (hhF v) (hF v).continuous t
  have hAmp (v : V) (ξ : Fin r → ℝ) : ‖A v ξ‖ₑ ≤ Fourier.mixedFourierEnvelope00 F ξ := by
    have hn : ‖A v ξ‖ = ‖Fourier.timeFourier (fun t => F t v) ξ‖ := by
      simp only [A, norm_mul, Circle.norm_coe, one_mul]
    rw [← ofReal_norm, hn, ofReal_norm]
    exact le_iSup (fun v => ‖Fourier.timeFourier (fun t => F t v) ξ‖ₑ) v
  have hs := mixedFourierNorm00_integral_dominated_le volume θ A (fun t ξ => frozenModulation χ j t ξ)
    hK (integrable_frozenModulation hχ hcχ j) hj (Fourier.measurable_mixedFourierEnvelope00 hiF) hAmp
  have hEq : (fun t v => cutoffTimeTrace χ j (c v) (fun u => F u v) t) =
      (fun t v => ∫ ξ, A v ξ * frozenModulation χ j t ξ) := funext (fun t => funext (he t))
  rw [← hEq] at hs
  apply hs.trans
  calc
    _ ≤ ∫⁻ ξ, Fourier.mixedFourierEnvelope00 F ξ *
        (ENNReal.ofReal (2 ^ θ) * Fourier.timeWeight θ ξ *
          Fourier.timeFourierNorm θ (Fourier.coordinateCutoff (r := r) χ)) :=
      lintegral_mono (fun ξ => mul_le_mul' le_rfl (timeFourierNorm_frozenModulation_le hθ χ j ξ))
    _ = ∫⁻ ξ, (ENNReal.ofReal (2 ^ θ) * Fourier.timeFourierNorm θ (Fourier.coordinateCutoff (r := r) χ)) *
        (Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 F ξ) := by
      apply lintegral_congr
      intro ξ
      ac_rfl
    _ = _ := by
      rw [Fourier.mixedFourierNorm00_eq_lintegral hiF]
      exact lintegral_const_mul _ ((Fourier.timeWeight_measurable θ).mul
        (Fourier.measurable_mixedFourierEnvelope00 hiF))

end WaveTurbulence.Incoh
