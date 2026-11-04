/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RectanglePhaseLimit
public import WaveTurbulence.Foundations.Incoh.SmoothRectanglePhase
public import WaveTurbulence.Foundations.Incoh.MixedFourierFatou
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform phase bounds for literal rectangular fibers

TARGET (incohproof27)–(incohproof28): hard interval boundaries are admitted
by a proved limiting argument. Arbitrary momentum dependence of phases
and endpoints is retained inside the mixed Fourier norm.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology ENNReal

namespace WaveTurbulence.Incoh

/-- The triangular and fourfold phase bounds for the literal rectangle indicator. -/
theorem exists_rectangle_phase_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (Γ₁ Γ₂ : Mom d → ℝ) (a b : Mom d → Fin 2 → ℝ),
      (∀ k, a k ≤ b k) →
      Fourier.mixedFourierNorm (1 / 4) 0 0
        (Fourier.cutoffU χ Γ₁ (fun t k => rectangleIndicator (a k) (b k) t)) ≤ ENNReal.ofReal C ∧
      Fourier.mixedFourierNorm (1 / 4) 0 0
        (Fourier.cutoffV χ Γ₁ Γ₂ (fun t k => rectangleIndicator (a k) (b k) t)) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := exists_smoothRectangle_phase_bound hχ hcχ
  obtain ⟨h⟩ := Fourier.exists_cutoffControl hχ hcχ
  refine ⟨C, hC, ?_⟩
  intro d Γ₁ Γ₂ a b hab
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F := fun t k => rectangleIndicator (a k) (b k) t
  let Fₙ := fun n t k => smoothRectangle (ε n) (a k) (b k) t
  have hU (k : Mom d) : Integrable (fun t => Fourier.cutoffU χ Γ₁ F t k) ∧
      ∀ ξ, Tendsto (fun n => Fourier.timeFourier (fun t => Fourier.cutoffU χ Γ₁ (Fₙ n) t k) ξ)
        atTop (𝓝 (Fourier.timeFourier (fun t => Fourier.cutoffU χ Γ₁ F t k) ξ)) := by
    simp only [Fourier.cutoffU_eq_balanced]
    exact rectangle_balanced_fourier_limit hχ h hε hlim (a k) (b k) (hab k) 2 ![Γ₁ k, -Γ₁ k] 0 1
  have hV (k : Mom d) : Integrable (fun t => Fourier.cutoffV χ Γ₁ Γ₂ F t k) ∧
      ∀ ξ, Tendsto (fun n => Fourier.timeFourier (fun t => Fourier.cutoffV χ Γ₁ Γ₂ (Fₙ n) t k) ξ)
        atTop (𝓝 (Fourier.timeFourier (fun t => Fourier.cutoffV χ Γ₁ Γ₂ F t k) ξ)) := by
    simp only [Fourier.cutoffV_eq_balanced]
    exact rectangle_balanced_fourier_limit hχ h hε hlim (a k) (b k) (hab k) 4
      ![Γ₁ k, -Γ₁ k, Γ₂ k, -Γ₂ k] 1 2
  have hiU (n : ℕ) (k : Mom d) : Integrable (fun t => Fourier.cutoffU χ Γ₁ (Fₙ n) t k) := by
    rw [Fourier.cutoffU_eq_balanced]
    exact (Fourier.weightedOrderedIntegral_contDiff hχ hχ
      (Fourier.balancedCutoffAmplitude_contDiff hχ (contDiff_smoothRectangle (ε n) (a k) (b k)) _ _ _)).continuous.integrable_of_hasCompactSupport
      (Fourier.weightedOrderedIntegral_hasCompactSupport h.endpointBounds h.endpointBounds _)
  have hiV (n : ℕ) (k : Mom d) : Integrable (fun t => Fourier.cutoffV χ Γ₁ Γ₂ (Fₙ n) t k) := by
    rw [Fourier.cutoffV_eq_balanced]
    exact (Fourier.weightedOrderedIntegral_contDiff hχ hχ
      (Fourier.balancedCutoffAmplitude_contDiff hχ (contDiff_smoothRectangle (ε n) (a k) (b k)) _ _ _)).continuous.integrable_of_hasCompactSupport
      (Fourier.weightedOrderedIntegral_hasCompactSupport h.endpointBounds h.endpointBounds _)
  rw [← Fourier.mixedFourierNorm00_eq_mixedFourierNorm, ← Fourier.mixedFourierNorm00_eq_mixedFourierNorm]
  constructor
  · apply mixedFourierNorm00_le_of_fourier_tendsto (1 / 4) (fun k => (hU k).1) hiU (fun k => (hU k).2)
    intro n
    rw [Fourier.mixedFourierNorm00_eq_mixedFourierNorm]
    exact (hb d Γ₁ Γ₂ a b hab (ε n) (hε n)).1
  · apply mixedFourierNorm00_le_of_fourier_tendsto (1 / 4) (fun k => (hV k).1) hiV (fun k => (hV k).2)
    intro n
    rw [Fourier.mixedFourierNorm00_eq_mixedFourierNorm]
    exact (hb d Γ₁ Γ₂ a b hab (ε n) (hε n)).2

end WaveTurbulence.Incoh
