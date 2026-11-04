/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothCausalBoxBound
public import WaveTurbulence.Foundations.Incoh.WeightedOrderedLimit
public import WaveTurbulence.Foundations.Incoh.MixedFourierFatou
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quarter regularity of the literal causal box kernels

TARGET (incohproof28) with all selected-clock layer bounds retained. The
hard causal ordering and interval indicators are obtained by bounded limits,
so no smoothness assertion about the source time domain is used.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace WaveTurbulence.Incoh

/-- Both two-clock and four-clock causal box kernels have a uniform mixed quarter norm. -/
theorem exists_causalBoxKernel_bound (m : ℕ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ,
      ∀ phase a b : Mom d → Fin (m + 2) → ℝ,
      (∀ k, ∑ j, phase k j = 0) → (∀ k, a k ≤ b k) →
      Fourier.mixedFourierNorm00 (1 / 4) (fun t k => causalBoxKernel m χ (phase k) (a k) (b k) t) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := exists_smoothCausalBoxKernel_bound m hχ hcχ
  obtain ⟨h⟩ := Fourier.exists_cutoffControl hχ hcχ
  refine ⟨C, hC, ?_⟩
  intro d phase a b hp hab
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hA (n : ℕ) (k : Mom d) : ContDiff ℝ ∞ (smoothCausalBoxAmplitude m χ (ε n) (phase k) (a k) (b k)) :=
    contDiff_smoothCausalBoxAmplitude m hχ (ε n) (phase k) (a k) (b k)
  have hL (k : Mom d) := weightedOrderedIntegral_fourier_limit hχ h (m + 2)
    (pow_nonneg (zero_le_one.trans h.one_le_bound) (m + 2))
    (fun n => hA n k)
    (fun n v => norm_smoothCausalBoxAmplitude_le m h (hε n) (phase k) (a k) (b k) (hab k) v)
    (fun v => tendsto_smoothCausalBoxAmplitude m χ hε hlim (phase k) (a k) (b k) (hab k) v)
  have hi (n : ℕ) (k : Mom d) : Integrable (smoothCausalBoxKernel m χ (ε n) (phase k) (a k) (b k)) :=
    (Fourier.weightedOrderedIntegral_contDiff hχ hχ (hA n k)).continuous.integrable_of_hasCompactSupport
      (Fourier.weightedOrderedIntegral_hasCompactSupport h.endpointBounds h.endpointBounds _)
  apply mixedFourierNorm00_le_of_fourier_tendsto (1 / 4) (fun k => (hL k).1) hi (fun k => (hL k).2)
  intro n
  exact hb d phase a b hp hab (ε n) (hε n)

end WaveTurbulence.Incoh
