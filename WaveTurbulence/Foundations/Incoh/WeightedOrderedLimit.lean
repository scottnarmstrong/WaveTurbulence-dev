/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.OrderedIntegralLimit
public import WaveTurbulence.Foundations.Incoh.TimeFourierDominated
public import WaveTurbulence.Foundations.Fourier.WeightedSupport

/-!
# Fourier convergence of cutoff ordered integrals

Bounded smooth amplitudes may converge to hard interval indicators. The
fixed output cutoff supplies a common integrable time dominator.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- The cutoff ordered integral has an explicit compactly supported dominator. -/
theorem norm_weightedOrderedIntegral_le_indicator {χ : ℝ → ℝ}
    (h : Fourier.CutoffControl χ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (F : (Fin n → ℝ) → ℂ) (hF : ∀ v, ‖F v‖ ≤ C) (t : Fin 2 → ℝ) :
    ‖Fourier.weightedOrderedIntegral n χ χ F t‖ ≤
      (Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius)).indicator
        (fun _ => h.bound ^ 2 * (C * (2 * h.radius) ^ n)) t := by
  by_cases ht : t ∈ Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius)
  · rw [indicator_of_mem ht]
    rw [Fourier.weightedOrderedIntegral, norm_mul]
    have hp := (Fourier.mem_two_time_box_iff h.radius t).mp ht
    exact mul_le_mul (Fourier.norm_endpoint_product_le (zero_le_one.trans h.one_le_bound)
      h.endpointBounds h.endpointBounds t)
      (norm_orderedIntegral_le n hC (zero_le_one.trans h.one_le_radius) F hF
        (abs_le.mp hp.1) (abs_le.mp hp.2)) (norm_nonneg _) (sq_nonneg _)
  · rw [indicator_of_notMem ht, Fourier.weightedOrderedIntegral,
      Fourier.endpoint_product_eq_zero_outside h.endpointBounds h.endpointBounds t ht,
      zero_mul, norm_zero]

/-- Cutoff ordered integration preserves bounded pointwise limits in physical and Fourier space. -/
theorem weightedOrderedIntegral_fourier_limit {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : Fourier.CutoffControl χ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    {Fₙ : ℕ → (Fin n → ℝ) → ℂ} {F : (Fin n → ℝ) → ℂ}
    (hd : ∀ j, ContDiff ℝ ∞ (Fₙ j)) (hb : ∀ j v, ‖Fₙ j v‖ ≤ C)
    (hl : ∀ v, Tendsto (fun j => Fₙ j v) atTop (𝓝 (F v))) :
    Integrable (Fourier.weightedOrderedIntegral n χ χ F) ∧ ∀ ξ,
      Tendsto (fun j => Fourier.timeFourier (Fourier.weightedOrderedIntegral n χ χ (Fₙ j)) ξ)
        atTop (𝓝 (Fourier.timeFourier (Fourier.weightedOrderedIntegral n χ χ F) ξ)) := by
  let B := (Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius)).indicator
    (fun _ => h.bound ^ 2 * (C * (2 * h.radius) ^ n))
  have hB : Integrable B := by
    change Integrable ((Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius)).indicator
      (fun _ => h.bound ^ 2 * (C * (2 * h.radius) ^ n)))
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  apply integrable_and_timeFourier_tendsto_of_dominated
    (fun j => (Fourier.weightedOrderedIntegral_contDiff hχ hχ (hd j)).continuous.aestronglyMeasurable)
    hB (fun j t => norm_weightedOrderedIntegral_le_indicator h n hC (Fₙ j) (hb j) t)
  intro t
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
