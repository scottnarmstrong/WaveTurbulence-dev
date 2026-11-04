/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BalancedAmplitude
public import WaveTurbulence.Foundations.Fourier.BoxIntegralLinearity
import Mathlib.Tactic

/-!
# Fixed-box bounds for balanced oscillatory amplitudes

The amplitude and its diagonal derivative are estimated by the source
function and its two first partial derivatives on the same fixed box.
No coefficient of the balanced phase enters these bounds.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The balanced amplitude box integral is bounded by the source-coordinate marginal. -/
theorem boxIntegral_balancedCutoffAmplitude_le {n : ℕ} {χ : ℝ → ℝ} (h : CutoffControl χ)
    (a : Fin n → ℝ) (F : (Fin 2 → ℝ) → ℂ) (i j : Fin n) (R : ℝ) :
    boxIntegral n (fun v => ‖balancedCutoffAmplitude χ a F i j v‖ₑ) R ≤
      ENNReal.ofReal (h.bound ^ n) * boxIntegral n (fun v => ‖F ![v i, v j]‖ₑ) R := by
  have hC : 0 ≤ h.bound := le_trans zero_le_one h.one_le_bound
  calc
    _ ≤ boxIntegral n (fun v => ENNReal.ofReal (h.bound ^ n) * ‖F ![v i, v j]‖ₑ) R := by
      apply boxIntegral_mono n
      intro v
      calc
        _ = ENNReal.ofReal ‖balancedCutoffAmplitude χ a F i j v‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (h.bound ^ n * ‖F ![v i, v j]‖) :=
          ENNReal.ofReal_le_ofReal (norm_balancedCutoffAmplitude_le h a F i j v)
        _ = _ := by rw [ENNReal.ofReal_mul (pow_nonneg hC n), ofReal_norm]
    _ = _ := boxIntegral_const_mul n _ ENNReal.ofReal_ne_top _ R

/-- The diagonal amplitude box integral costs only the source amplitude and first-derivative marginals. -/
theorem boxIntegral_diagonal_balancedCutoffAmplitude_le {n : ℕ} {χ : ℝ → ℝ}
    {F : (Fin 2 → ℝ) → ℂ} (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F)
    (h : CutoffControl χ) {a : Fin n → ℝ} (ha : ∑ k, a k = 0) (i j : Fin n) (R : ℝ) :
    boxIntegral n (fun v => ‖timeDirectionalDerivative (fun _ => 1)
        (balancedCutoffAmplitude χ a F i j) v‖ₑ) R ≤
      ENNReal.ofReal ((n : ℝ) * h.bound ^ (n + 1)) * boxIntegral n (fun v => ‖F ![v i, v j]‖ₑ) R +
      ENNReal.ofReal (h.bound ^ n) *
        (boxIntegral n (fun v => ‖WaveTurbulence.partialDeriv 0 F ![v i, v j]‖ₑ) R +
          boxIntegral n (fun v => ‖WaveTurbulence.partialDeriv 1 F ![v i, v j]‖ₑ) R) := by
  let f₀ := fun v : Fin n → ℝ => ‖F ![v i, v j]‖ₑ
  let f₁ := fun v : Fin n → ℝ => ‖WaveTurbulence.partialDeriv 0 F ![v i, v j]‖ₑ
  let f₂ := fun v : Fin n → ℝ => ‖WaveTurbulence.partialDeriv 1 F ![v i, v j]‖ₑ
  let c₀ := ENNReal.ofReal ((n : ℝ) * h.bound ^ (n + 1))
  let c₁ := ENNReal.ofReal (h.bound ^ n)
  have hm₀ : Measurable f₀ := (hF.continuous.comp (contDiff_coordinate_pair i j).continuous).measurable.enorm
  have hm₁ : Measurable f₁ :=
    ((WaveTurbulence.contDiff_infty_partialDeriv hF 0).continuous.comp
      (contDiff_coordinate_pair i j).continuous).measurable.enorm
  have hC : 0 ≤ h.bound := le_trans zero_le_one h.one_le_bound
  have hc₀ : 0 ≤ (n : ℝ) * h.bound ^ (n + 1) := by positivity
  have hc₁ : 0 ≤ h.bound ^ n := by positivity
  have hpoint (v : Fin n → ℝ) : ‖timeDirectionalDerivative (fun _ => 1)
      (balancedCutoffAmplitude χ a F i j) v‖ₑ ≤ c₀ * f₀ v + c₁ * (f₁ v + f₂ v) := by
    calc
      _ = ENNReal.ofReal ‖timeDirectionalDerivative (fun _ => 1)
          (balancedCutoffAmplitude χ a F i j) v‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (((n : ℝ) * h.bound ^ (n + 1)) * ‖F ![v i, v j]‖ +
          h.bound ^ n * (‖WaveTurbulence.partialDeriv 0 F ![v i, v j]‖ +
            ‖WaveTurbulence.partialDeriv 1 F ![v i, v j]‖)) :=
        ENNReal.ofReal_le_ofReal (norm_diagonal_balancedCutoffAmplitude_le hχ hF h ha i j v)
      _ ≤ ENNReal.ofReal (((n : ℝ) * h.bound ^ (n + 1)) * ‖F ![v i, v j]‖) +
          ENNReal.ofReal (h.bound ^ n * (‖WaveTurbulence.partialDeriv 0 F ![v i, v j]‖ +
            ‖WaveTurbulence.partialDeriv 1 F ![v i, v j]‖)) := ENNReal.ofReal_add_le
      _ = _ := by
        rw [ENNReal.ofReal_mul hc₀, ENNReal.ofReal_mul hc₁,
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm]
  calc
    _ ≤ boxIntegral n (fun v => c₀ * f₀ v + c₁ * (f₁ v + f₂ v)) R := boxIntegral_mono n hpoint R
    _ = boxIntegral n (fun v => c₀ * f₀ v) R + boxIntegral n (fun v => c₁ * (f₁ v + f₂ v)) R :=
      boxIntegral_add n (measurable_const.mul hm₀) _ R
    _ = _ := by
      rw [boxIntegral_const_mul n _ ENNReal.ofReal_ne_top,
        boxIntegral_const_mul n _ ENNReal.ofReal_ne_top, boxIntegral_add n hm₁ f₂ R]

end WaveTurbulence.Fourier
