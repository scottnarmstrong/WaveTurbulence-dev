/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourierEndpoints
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic

/-!
# Bilinear Fourier endpoint bounds

The Fourier pairing `∫ f̂ g` has norm at most one both on `L¹ × L¹`
and on `(L¹ ∩ L²) × L²`. These are the concrete endpoint estimates
used by finite bilinear interpolation in the proof of TARGET L2370.
-/

public section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The integral Fourier pairing is bounded by the product of the two `L¹` norms. -/
theorem fourier_pairing_L1 {f g : V → ℂ} (hg : Integrable g) :
    ‖∫ ξ, 𝓕 f ξ * g ξ‖ ≤ (∫ x, ‖f x‖) * (∫ ξ, ‖g ξ‖) := by
  calc
    _ ≤ ∫ ξ, (∫ x, ‖f x‖) * ‖g ξ‖ :=
      norm_integral_le_of_norm_le (hg.norm.const_mul _) (ae_of_all _ fun ξ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (Real.norm_fourier_le_integral_norm f ξ) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

/-- The integral Fourier pairing is bounded by the product of the `L²` norms,
with no assumption on the Fourier transform's membership supplied by the caller. -/
theorem fourier_pairing_L2 {f g : V → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    ‖∫ ξ, 𝓕 f ξ * g ξ‖ₑ ≤ eLpNorm f 2 * eLpNorm g 2 := by
  calc
    _ ≤ ∫⁻ ξ, ‖𝓕 f ξ * g ξ‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ eLpNorm (fun ξ => 𝓕 f ξ * g ξ) 1 := lintegral_enorm_le_eLpNorm_one
    _ ≤ eLpNorm (𝓕 f) 2 * eLpNorm g 2 :=
      eLpNorm_smul_le_mul_eLpNorm_of_pos (𝕜 := ℂ) (φ := 𝓕 f) (f := g)
        (μ := (volume : Measure V)) (p := 2) (q := 2) (r := 1) (by norm_num)
    _ = _ := by rw [integral_fourier_eLpNorm_two hf hf2]

/-- Real-valued version of the bilinear `L²` endpoint. -/
theorem fourier_pairing_L2_real {f g : V → ℂ} (hf : Integrable f)
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) :
    ‖∫ ξ, 𝓕 f ξ * g ξ‖ ≤ lpNorm f 2 volume * lpNorm g 2 volume := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hf2.eLpNorm_ne_top hg2.eLpNorm_ne_top)
    (fourier_pairing_L2 (g := g) hf hf2)
  simpa only [ENNReal.toReal_mul, toReal_enorm, toReal_eLpNorm] using h

/-- Finite linearity of the ordinary Fourier integral. -/
theorem integral_fourier_finsetSum {ι : Type*} (s : Finset ι) (f : ι → V → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i)) (ξ : V) :
    𝓕 (fun x => ∑ i ∈ s, f i x) ξ = ∑ i ∈ s, 𝓕 (f i) ξ := by
  simp_rw [Real.fourier_eq, Finset.smul_sum]
  exact integral_finsetSum s fun i hi =>
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ V) continuous_inner ξ).mpr (hf i hi)

/-- Complex scalar linearity of the ordinary Fourier integral. -/
theorem integral_fourier_smul (c : ℂ) (f : V → ℂ) (ξ : V) :
    𝓕 (fun x => c • f x) ξ = c • 𝓕 f ξ := by
  exact congrFun (VectorFourier.fourierIntegral_const_smul
    Real.fourierChar volume (innerₗ V) f c) ξ

end WaveTurbulence.Fourier
