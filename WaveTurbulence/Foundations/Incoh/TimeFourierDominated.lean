/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeFourierLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated passage to the literal time Fourier transform

Used for ordered-integral approximations with discontinuous limiting inputs.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace WaveTurbulence.Incoh

/-- A common integrable dominator gives an integrable limit and Fourier convergence. -/
theorem integrable_and_timeFourier_tendsto_of_dominated {r : ℕ}
    {Fₙ : ℕ → (Fin r → ℝ) → ℂ} {F : (Fin r → ℝ) → ℂ}
    (hm : ∀ n, AEStronglyMeasurable (Fₙ n)) {B : (Fin r → ℝ) → ℝ}
    (hB : Integrable B) (hb : ∀ n x, ‖Fₙ n x‖ ≤ B x)
    (hl : ∀ x, Tendsto (fun n => Fₙ n x) atTop (𝓝 (F x))) :
    Integrable F ∧ ∀ ξ, Tendsto (fun n => Fourier.timeFourier (Fₙ n) ξ) atTop
      (𝓝 (Fourier.timeFourier F ξ)) := by
  have hFn (n : ℕ) : Integrable (Fₙ n) := hB.mono' (hm n) (Eventually.of_forall (hb n))
  have hFm : AEStronglyMeasurable F :=
    aestronglyMeasurable_of_tendsto_ae atTop hm (Eventually.of_forall hl)
  have hFb (x : Fin r → ℝ) : ‖F x‖ ≤ B x :=
    le_of_tendsto (hl x).norm (Eventually.of_forall (fun n => hb n x))
  refine ⟨hB.mono' hFm (Eventually.of_forall hFb), ?_⟩
  intro ξ
  change Tendsto (fun n => ∫ t, Real.fourierChar (-Fourier.timePairing r t ξ) • Fₙ n t)
    atTop (𝓝 (∫ t, Real.fourierChar (-Fourier.timePairing r t ξ) • F t))
  have hL : Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => Fourier.timePairing r p.1 p.2) := by
    change Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∑ j, p.1 j * p.2 j)
    fun_prop
  apply tendsto_integral_of_dominated_convergence B
  · intro n
    exact ((VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar hL ξ).mpr
      (hFn n)).aestronglyMeasurable
  · exact hB
  · intro n
    exact Eventually.of_forall (fun t => by simpa only [Circle.norm_smul] using hb n t)
  · exact Eventually.of_forall (fun t => (hl t).const_smul _)

end WaveTurbulence.Incoh
