/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MixedTimeTraceLimit
public import WaveTurbulence.Foundations.Fourier.BalancedAmplitude

/-!
# Two fixed endpoints in the mixed Fourier norm

Both endpoints may be fixed independently and depend on the vector parameter.
The argument uses smooth approximations and never differentiates hard boundaries.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace WaveTurbulence.Incoh

/-- Apply the fixed-clock limit estimate twice, paying the same cutoff factor twice. -/
theorem mixedFourierNorm00_cutoffTimeTrace_twice_limit_le {r : ℕ} {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {Fₙ : ℕ → (Fin r → ℝ) → V → ℂ} {F : (Fin r → ℝ) → V → ℂ}
    (hd : ∀ n v, ContDiff ℝ ∞ (fun t => Fₙ n t v))
    (hc : ∀ n v, HasCompactSupport (fun t => Fₙ n t v))
    {M : ℝ} (hb : ∀ n v t, ‖Fₙ n t v‖ ≤ M)
    (hl : ∀ v t, Tendsto (fun n => Fₙ n t v) atTop (𝓝 (F t v)))
    {C : ℝ≥0∞} (hC : ∀ n, Fourier.mixedFourierNorm00 θ (Fₙ n) ≤ C)
    (j₀ j₁ : Fin r) (c₀ c₁ : V → ℝ) :
    Fourier.mixedFourierNorm00 θ (fun t v => cutoffTimeTrace χ j₁ (c₁ v)
      (cutoffTimeTrace χ j₀ (c₀ v) (fun u => F u v)) t) ≤
      (ENNReal.ofReal (2 ^ θ) * Fourier.timeFourierNorm θ (Fourier.coordinateCutoff (r := r) χ)) *
        ((ENNReal.ofReal (2 ^ θ) * Fourier.timeFourierNorm θ (Fourier.coordinateCutoff (r := r) χ)) * C) := by
  obtain ⟨h⟩ := Fourier.exists_cutoffControl hχ hcχ
  let Gₙ := fun n t v => cutoffTimeTrace χ j₀ (c₀ v) (fun u => Fₙ n u v) t
  have hdG (n : ℕ) (v : V) : ContDiff ℝ ∞ (fun t => Gₙ n t v) :=
    contDiff_cutoffTimeTrace hχ (hd n v) j₀ (c₀ v)
  have hcG (n : ℕ) (v : V) : HasCompactSupport (fun t => Gₙ n t v) :=
    hasCompactSupport_cutoffTimeTrace hcχ j₀ (c₀ v) _
  have hbG (n : ℕ) (v : V) (t : Fin r → ℝ) :
      ‖Gₙ n t v‖ ≤ h.bound ^ r * max M 0 := by
    apply (norm_cutoffTimeTrace_le χ j₀ (c₀ v) (fun u => hb n v u) t).trans
    exact (mul_le_mul_of_nonneg_left (le_max_left M 0) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (Fourier.norm_coordinateCutoff_le h t) (le_max_right M 0))
  have hlG (v : V) (t : Fin r → ℝ) : Tendsto (fun n => Gₙ n t v) atTop
      (𝓝 (cutoffTimeTrace χ j₀ (c₀ v) (fun u => F u v) t)) :=
    (hl v (Function.update t j₀ (c₀ v))).const_mul _
  have hCG (n : ℕ) : Fourier.mixedFourierNorm00 θ (Gₙ n) ≤
      (ENNReal.ofReal (2 ^ θ) * Fourier.timeFourierNorm θ (Fourier.coordinateCutoff (r := r) χ)) * C :=
    (mixedFourierNorm00_cutoffTimeTrace_le hθ hχ hcχ (Fₙ n) (hd n) (hc n) j₀ c₀).trans
      (mul_le_mul' le_rfl (hC n))
  exact mixedFourierNorm00_cutoffTimeTrace_limit_le hθ hχ hcχ hdG hcG hbG hlG hCG j₁ c₁

end WaveTurbulence.Incoh
