/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RectangleKernelMeasurable
public import WaveTurbulence.Foundations.Incoh.WeightedOrderedLimit

/-!
# A common time dominator for all rectangular phase kernels

This bound is uniform in phases and interval endpoints. It supplies joint
integrability for actual internal-clock mixtures.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Every literal rectangle indicator has modulus at most one. -/
theorem norm_rectangleIndicator_le_one (a b t : Fin 2 → ℝ) :
    ‖rectangleIndicator a b t‖ ≤ 1 := by
  classical
  by_cases h0 : t 0 ∈ Ioc (a 0) (b 0) <;>
    by_cases h1 : t 1 ∈ Ioc (a 1) (b 1) <;> simp [rectangleIndicator, h0, h1]

/-- The explicit time dominator for an `m`-fold rectangular phase kernel. -/
@[expose] def rectangleKernelDominator {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (m : ℕ) : (Fin 2 → ℝ) → ℝ :=
  (Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius)).indicator
    (fun _ => h.bound ^ 2 * (h.bound ^ m * (2 * h.radius) ^ m))

theorem integrable_rectangleKernelDominator {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ) (m : ℕ) :
    Integrable (rectangleKernelDominator h m) := by
  unfold rectangleKernelDominator
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const isCompact_Icc.measure_ne_top

/-- The same dominator works for every phase and every rectangular fiber. -/
theorem norm_rectangleOrderedKernel_le {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (m : ℕ) (phase : Fin m → ℝ) (a b : Fin 2 → ℝ) (i j : Fin m) (t : Fin 2 → ℝ) :
    ‖Fourier.weightedOrderedIntegral m χ χ
      (Fourier.balancedCutoffAmplitude χ phase (rectangleIndicator a b) i j) t‖ ≤
        rectangleKernelDominator h m t := by
  apply norm_weightedOrderedIntegral_le_indicator h m (pow_nonneg (zero_le_one.trans h.one_le_bound) m)
  intro v
  exact (Fourier.norm_balancedCutoffAmplitude_le h phase _ i j v).trans
    ((mul_le_mul_of_nonneg_left (norm_rectangleIndicator_le_one a b _)
      (pow_nonneg (zero_le_one.trans h.one_le_bound) m)).trans_eq (mul_one _))

/-- The universal triangular family has a common integrable time bound. -/
theorem norm_universalRectangleU_le {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (p : Mom 6) (t : Fin 2 → ℝ) :
    ‖universalRectangleU χ t p‖ ≤ rectangleKernelDominator h 2 t := by
  have he := congrFun (Fourier.cutoffU_eq_balanced χ (fun p : Mom 6 => p 0)
    (fun t p => rectangleIndicator (rectanglePhaseLower p) (rectanglePhaseUpper p) t) p) t
  change ‖Fourier.cutoffU χ (fun p : Mom 6 => p 0)
    (fun t p => rectangleIndicator (rectanglePhaseLower p) (rectanglePhaseUpper p) t) t p‖ ≤ _
  rw [he]
  exact norm_rectangleOrderedKernel_le h 2 _ _ _ 0 1 t

/-- The universal fourfold family has the corresponding common time bound. -/
theorem norm_universalRectangleV_le {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (p : Mom 6) (t : Fin 2 → ℝ) :
    ‖universalRectangleV χ t p‖ ≤ rectangleKernelDominator h 4 t := by
  have he := congrFun (Fourier.cutoffV_eq_balanced χ (fun p : Mom 6 => p 0) (fun p : Mom 6 => p 1)
    (fun t p => rectangleIndicator (rectanglePhaseLower p) (rectanglePhaseUpper p) t) p) t
  change ‖Fourier.cutoffV χ (fun p : Mom 6 => p 0) (fun p : Mom 6 => p 1)
    (fun t p => rectangleIndicator (rectanglePhaseLower p) (rectanglePhaseUpper p) t) t p‖ ≤ _
  rw [he]
  exact norm_rectangleOrderedKernel_le h 4 _ _ _ 1 2 t

end WaveTurbulence.Incoh
