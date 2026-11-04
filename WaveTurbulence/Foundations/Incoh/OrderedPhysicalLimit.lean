/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.WeightedOrderedLimit

/-!
# Pointwise limits and uniform bounds for cutoff ordered integrals

These statements apply at fixed integer endpoints as well as moving clocks.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- Uniform boundedness of a cutoff ordered integral in every output clock. -/
theorem norm_weightedOrderedIntegral_le_const {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C) (F : (Fin n → ℝ) → ℂ) (hF : ∀ v, ‖F v‖ ≤ C)
    (t : Fin 2 → ℝ) : ‖Fourier.weightedOrderedIntegral n χ χ F t‖ ≤
      h.bound ^ 2 * (C * (2 * h.radius) ^ n) := by
  apply (norm_weightedOrderedIntegral_le_indicator h n hC F hF t).trans
  by_cases ht : t ∈ Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius)
  · rw [indicator_of_mem ht]
  · rw [indicator_of_notMem ht]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg hC (pow_nonneg
      (mul_nonneg (by norm_num) (zero_le_one.trans h.one_le_radius)) n))

/-- Bounded smooth amplitude convergence holds pointwise at every output clock pair. -/
theorem tendsto_weightedOrderedIntegral_of_bounded {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C) {Fₙ : ℕ → (Fin n → ℝ) → ℂ} {F : (Fin n → ℝ) → ℂ}
    (hd : ∀ j, ContDiff ℝ ∞ (Fₙ j)) (hb : ∀ j v, ‖Fₙ j v‖ ≤ C)
    (hl : ∀ v, Tendsto (fun j => Fₙ j v) atTop (𝓝 (F v))) (t : Fin 2 → ℝ) :
    Tendsto (fun j => Fourier.weightedOrderedIntegral n χ χ (Fₙ j) t) atTop
      (𝓝 (Fourier.weightedOrderedIntegral n χ χ F t)) := by
  by_cases ht : t ∈ Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius)
  · have hp := (Fourier.mem_two_time_box_iff h.radius t).mp ht
    exact (tendsto_orderedIntegral_of_bounded n hC (zero_le_one.trans h.one_le_radius)
      hd hb hl (abs_le.mp hp.1) (abs_le.mp hp.2)).const_mul _
  · have hz (G : (Fin n → ℝ) → ℂ) : Fourier.weightedOrderedIntegral n χ χ G t = 0 := by
      rw [Fourier.weightedOrderedIntegral,
        Fourier.endpoint_product_eq_zero_outside h.endpointBounds h.endpointBounds t ht, zero_mul]
    simp only [hz]
    exact tendsto_const_nhds

end WaveTurbulence.Incoh
