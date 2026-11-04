/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.OrderedPhysicalLimit
public import WaveTurbulence.Foundations.Incoh.RectangleIndicator
public import WaveTurbulence.Foundations.Fourier.BalancedAmplitude

/-!
# Pointwise rectangular-kernel approximation at every endpoint

The bounds are uniform in phases. In particular the approximation remains
valid when either external endpoint is frozen at an integer layer boundary.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- Uniform time bound for every smooth rectangular ordered phase kernel. -/
theorem norm_smoothRectangleOrderedKernel_le {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    {ε : ℝ} (hε : 0 < ε) (a b : Fin 2 → ℝ) (hab : a ≤ b)
    (m : ℕ) (phase : Fin m → ℝ) (i j : Fin m) (t : Fin 2 → ℝ) :
    ‖Fourier.weightedOrderedIntegral m χ χ
      (Fourier.balancedCutoffAmplitude χ phase (smoothRectangle ε a b) i j) t‖ ≤
      h.bound ^ 2 * (h.bound ^ m * (2 * h.radius) ^ m) := by
  apply norm_weightedOrderedIntegral_le_const h m (pow_nonneg (zero_le_one.trans h.one_le_bound) m)
  intro v
  exact (Fourier.norm_balancedCutoffAmplitude_le h phase _ i j v).trans
    ((mul_le_mul_of_nonneg_left (norm_smoothRectangle_le_one hε a b _ hab)
      (pow_nonneg (zero_le_one.trans h.one_le_bound) m)).trans_eq (mul_one _))

/-- Exact pointwise convergence, including at every fixed external endpoint. -/
theorem tendsto_rectangleOrderedKernel {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : Fourier.CutoffControl χ) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (a b : Fin 2 → ℝ) (hab : a ≤ b)
    (m : ℕ) (phase : Fin m → ℝ) (i j : Fin m) (t : Fin 2 → ℝ) :
    Tendsto (fun n => Fourier.weightedOrderedIntegral m χ χ
      (Fourier.balancedCutoffAmplitude χ phase (smoothRectangle (ε n) a b) i j) t) atTop
      (𝓝 (Fourier.weightedOrderedIntegral m χ χ
        (Fourier.balancedCutoffAmplitude χ phase (rectangleIndicator a b) i j) t)) := by
  apply tendsto_weightedOrderedIntegral_of_bounded h m
    (pow_nonneg (zero_le_one.trans h.one_le_bound) m)
  · intro n
    exact Fourier.balancedCutoffAmplitude_contDiff hχ (contDiff_smoothRectangle (ε n) a b) phase i j
  · intro n v
    exact (Fourier.norm_balancedCutoffAmplitude_le h phase _ i j v).trans
      ((mul_le_mul_of_nonneg_left (norm_smoothRectangle_le_one (hε n) a b _ hab)
        (pow_nonneg (zero_le_one.trans h.one_le_bound) m)).trans_eq (mul_one _))
  · intro v
    exact (tendsto_smoothRectangle hε hlim a b hab ![v i, v j]).const_mul _

end WaveTurbulence.Incoh
