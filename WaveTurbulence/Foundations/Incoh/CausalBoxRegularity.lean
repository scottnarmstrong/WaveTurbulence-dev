/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalBoxBound
public import WaveTurbulence.Foundations.Incoh.RectangleKernelDominator

/-!
# Pointwise approximation and domination of literal causal box kernels

These properties supply the source-domain identifications and actual
Fubini premises for mixing the causal kernels against the remaining links.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- The hard amplitude has the same phase-independent pointwise bound. -/
theorem norm_causalBoxAmplitude_le (m : ℕ) {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (phase a b : Fin (m + 2) → ℝ) (hab : a ≤ b) (v : Fin (m + 2) → ℝ) :
    ‖causalBoxAmplitude m χ phase a b v‖ ≤ h.bound ^ (m + 2) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto (tendsto_smoothCausalBoxAmplitude m χ hε hlim phase a b hab v).norm
    (Filter.Eventually.of_forall (fun n => norm_smoothCausalBoxAmplitude_le m h (hε n) phase a b hab v))

/-- One common integrable time dominator works for every phase and every interval endpoint. -/
theorem norm_causalBoxKernel_le (m : ℕ) {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (phase a b : Fin (m + 2) → ℝ) (hab : a ≤ b) (t : Fin 2 → ℝ) :
    ‖causalBoxKernel m χ phase a b t‖ ≤ rectangleKernelDominator h (m + 2) t :=
  norm_weightedOrderedIntegral_le_indicator h (m + 2)
    (pow_nonneg (zero_le_one.trans h.one_le_bound) (m + 2)) _
    (norm_causalBoxAmplitude_le m h phase a b hab) t

end WaveTurbulence.Incoh
