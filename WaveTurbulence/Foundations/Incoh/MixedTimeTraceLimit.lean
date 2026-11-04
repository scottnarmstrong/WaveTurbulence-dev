/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MixedTimeTraceBound
public import WaveTurbulence.Foundations.Incoh.TimeTraceBasic
public import WaveTurbulence.Foundations.Incoh.MixedFourierFatou
public import WaveTurbulence.Foundations.Incoh.TimeFourierDominated

/-!
# Fixed-clock trace bounds for bounded pointwise limits

This passes the trace estimate from smooth approximations to kernels with
hard interval boundaries, without asserting smoothness of those boundaries.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace WaveTurbulence.Incoh

/-- Uniform smooth trace estimates pass to bounded pointwise limits. -/
theorem mixedFourierNorm00_cutoffTimeTrace_limit_le {r : ℕ} {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {Fₙ : ℕ → (Fin r → ℝ) → V → ℂ} {F : (Fin r → ℝ) → V → ℂ}
    (hd : ∀ n v, ContDiff ℝ ∞ (fun t => Fₙ n t v))
    (hc : ∀ n v, HasCompactSupport (fun t => Fₙ n t v))
    {M : ℝ} (hb : ∀ n v t, ‖Fₙ n t v‖ ≤ M)
    (hl : ∀ v t, Tendsto (fun n => Fₙ n t v) atTop (𝓝 (F t v)))
    {C : ℝ≥0∞} (hC : ∀ n, Fourier.mixedFourierNorm00 θ (Fₙ n) ≤ C)
    (j : Fin r) (c : V → ℝ) :
    Fourier.mixedFourierNorm00 θ (fun t v => cutoffTimeTrace χ j (c v) (fun u => F u v) t) ≤
      (ENNReal.ofReal (2 ^ θ) * Fourier.timeFourierNorm θ (Fourier.coordinateCutoff (r := r) χ)) * C := by
  let Gₙ := fun n t v => cutoffTimeTrace χ j (c v) (fun u => Fₙ n u v) t
  let G := fun t v => cutoffTimeTrace χ j (c v) (fun u => F u v) t
  have hlim (v : V) (t : Fin r → ℝ) : Tendsto (fun n => Gₙ n t v) atTop (𝓝 (G t v)) :=
    (hl v (Function.update t j (c v))).const_mul _
  have hdG (n : ℕ) (v : V) : ContDiff ℝ ∞ (fun t => Gₙ n t v) :=
    contDiff_cutoffTimeTrace hχ (hd n v) j (c v)
  have hcG (n : ℕ) (v : V) : HasCompactSupport (fun t => Gₙ n t v) :=
    hasCompactSupport_cutoffTimeTrace hcχ j (c v) _
  have hiG (n : ℕ) (v : V) : Integrable (fun t => Gₙ n t v) :=
    (hdG n v).continuous.integrable_of_hasCompactSupport (hcG n v)
  have hGl (v : V) := integrable_and_timeFourier_tendsto_of_dominated
    (fun n => (hdG n v).continuous.aestronglyMeasurable)
    (integrable_timeTrace_dominator hχ hcχ M)
    (fun n t => norm_cutoffTimeTrace_le χ j (c v) (fun u => hb n v u) t) (hlim v)
  apply mixedFourierNorm00_le_of_fourier_tendsto θ (fun v => (hGl v).1) hiG (fun v => (hGl v).2)
  intro n
  exact (mixedFourierNorm00_cutoffTimeTrace_le hθ hχ hcχ (Fₙ n) (hd n) (hc n) j c).trans
    (mul_le_mul' le_rfl (hC n))

end WaveTurbulence.Incoh
