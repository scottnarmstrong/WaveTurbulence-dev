/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.UniversalRectanglePhase
public import WaveTurbulence.Foundations.Incoh.RectangleOrderedPhysicalLimit
public import WaveTurbulence.Foundations.Fourier.WeightedSupport

/-!
# Smooth approximations of the universal fourfold rectangular family

Their time bound and quarter-regularity norm are uniform in the smoothing
width and in all six phase/endpoint parameters.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace WaveTurbulence.Incoh

/-- Smooth only the literal rectangular input, retaining both arbitrary phases. -/
@[expose] def smoothUniversalRectangleV (χ : ℝ → ℝ) (ε : ℝ) : (Fin 2 → ℝ) → Mom 6 → ℂ :=
  Fourier.cutoffV χ (fun p => p 0) (fun p => p 1)
    (fun t p => smoothRectangle ε (rectanglePhaseLower p) (rectanglePhaseUpper p) t)

theorem smoothUniversalRectangleV_eq_weighted (χ : ℝ → ℝ) (ε : ℝ) (p : Mom 6) :
    (fun t => smoothUniversalRectangleV χ ε t p) = Fourier.weightedOrderedIntegral 4 χ χ
      (Fourier.balancedCutoffAmplitude χ ![p 0, -p 0, p 1, -p 1]
        (smoothRectangle ε (rectanglePhaseLower p) (rectanglePhaseUpper p)) 1 2) :=
  Fourier.cutoffV_eq_balanced χ (fun p : Mom 6 => p 0) (fun p : Mom 6 => p 1) _ p

theorem contDiff_smoothUniversalRectangleV {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (ε : ℝ) (p : Mom 6) : ContDiff ℝ ∞ (fun t => smoothUniversalRectangleV χ ε t p) := by
  rw [smoothUniversalRectangleV_eq_weighted]
  exact Fourier.weightedOrderedIntegral_contDiff hχ hχ
    (Fourier.balancedCutoffAmplitude_contDiff hχ (contDiff_smoothRectangle ε _ _) _ _ _)

theorem hasCompactSupport_smoothUniversalRectangleV {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (ε : ℝ) (p : Mom 6) : HasCompactSupport (fun t => smoothUniversalRectangleV χ ε t p) := by
  rw [smoothUniversalRectangleV_eq_weighted]
  exact Fourier.weightedOrderedIntegral_hasCompactSupport h.endpointBounds h.endpointBounds _

theorem norm_smoothUniversalRectangleV_le {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    {ε : ℝ} (hε : 0 < ε) (p : Mom 6) (t : Fin 2 → ℝ) :
    ‖smoothUniversalRectangleV χ ε t p‖ ≤ h.bound ^ 2 * (h.bound ^ 4 * (2 * h.radius) ^ 4) := by
  rw [congrFun (smoothUniversalRectangleV_eq_weighted χ ε p) t]
  exact norm_smoothRectangleOrderedKernel_le h hε _ _ (rectanglePhaseLower_le_upper p) 4 _ 1 2 t

/-- Exact pointwise approximation at every output endpoint. -/
theorem tendsto_smoothUniversalRectangleV {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : Fourier.CutoffControl χ) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (p : Mom 6) (t : Fin 2 → ℝ) :
    Tendsto (fun n => smoothUniversalRectangleV χ (ε n) t p) atTop (𝓝 (universalRectangleV χ t p)) := by
  have he (n : ℕ) := congrFun (smoothUniversalRectangleV_eq_weighted χ (ε n) p) t
  have h0 := congrFun (Fourier.cutoffV_eq_balanced χ (fun p : Mom 6 => p 0) (fun p : Mom 6 => p 1)
    (fun t p => rectangleIndicator (rectanglePhaseLower p) (rectanglePhaseUpper p) t) p) t
  change universalRectangleV χ t p = _ at h0
  simp_rw [he, h0]
  exact tendsto_rectangleOrderedKernel hχ h hε hlim _ _ (rectanglePhaseLower_le_upper p) 4 _ 1 2 t

/-- Uniform quarter-regularity, including the parameter supremum. -/
theorem exists_smoothUniversalRectangleV_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      Fourier.mixedFourierNorm00 (1 / 4) (smoothUniversalRectangleV χ ε) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := exists_smoothRectangle_phase_bound hχ hcχ
  refine ⟨C, hC, ?_⟩
  intro ε hε
  simpa only [smoothUniversalRectangleV, Fourier.mixedFourierNorm00_eq_mixedFourierNorm] using
    (hb 6 (fun p => p 0) (fun p => p 1) rectanglePhaseLower rectanglePhaseUpper
      rectanglePhaseLower_le_upper ε hε).2

end WaveTurbulence.Incoh
