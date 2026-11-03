/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeFourierLimit
import Mathlib.Tactic

/-!
# Closing weighted Fourier estimates along an approximating sequence

A finite common coefficient and a vanishing additive input error suffice
for the Fatou step, independently of any operator representation.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace WaveTurbulence.Fourier

/-- Fatou with quantitative approximating bounds and a vanishing additive error. -/
theorem timeFourierNorm_le_of_approximation_bound {r : ℕ} (θ : ℝ)
    {f : (Fin r → ℝ) → ℂ} {fₙ : ℕ → (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hfn : ∀ n, Integrable (fₙ n))
    (hlim : ∀ ξ, Tendsto (fun n => timeFourier (fₙ n) ξ) atTop (𝓝 (timeFourier f ξ)))
    {C M : ℝ≥0∞} (hC : C ≠ ⊤) {ε : ℕ → ℝ≥0∞} (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, timeFourierNorm θ (fₙ n) ≤ C * (M + ε n)) :
    timeFourierNorm θ f ≤ C * M := by
  have hsum : Tendsto (fun n => M + ε n) atTop (𝓝 M) := by
    simpa only [add_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => M) atTop (𝓝 M)).add hε
  have hupper : Tendsto (fun n => C * (M + ε n)) atTop (𝓝 (C * M)) :=
    ENNReal.Tendsto.const_mul hsum (Or.inr hC)
  apply (timeFourierNorm_le_liminf_of_tendsto θ hf hfn hlim).trans
  calc
    _ ≤ liminf (fun n => C * (M + ε n)) atTop :=
      liminf_le_liminf (Eventually.of_forall hbound)
    _ = _ := hupper.liminf_eq

end WaveTurbulence.Fourier
