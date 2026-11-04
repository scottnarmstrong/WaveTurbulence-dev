/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.WeightedOrderedLimit
public import WaveTurbulence.Foundations.Incoh.RectangleIndicator
public import WaveTurbulence.Foundations.Fourier.BalancedAmplitude

/-!
# Removing the smoothing from ordered rectangular phase kernels

All phase coefficients are arbitrary. The convergence argument requires
no differentiation of the hard time-order boundaries.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- Balanced phase kernels with literal rectangular fibers are the Fourier limits
of the smooth kernels, and their time slices are integrable. -/
theorem rectangle_balanced_fourier_limit {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : Fourier.CutoffControl χ) {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) (a b : Fin 2 → ℝ) (hab : a ≤ b)
    (m : ℕ) (phase : Fin m → ℝ) (i j : Fin m) :
    Integrable (Fourier.weightedOrderedIntegral m χ χ
      (Fourier.balancedCutoffAmplitude χ phase (rectangleIndicator a b) i j)) ∧
    ∀ ξ, Tendsto (fun n => Fourier.timeFourier (Fourier.weightedOrderedIntegral m χ χ
      (Fourier.balancedCutoffAmplitude χ phase (smoothRectangle (ε n) a b) i j)) ξ) atTop
      (𝓝 (Fourier.timeFourier (Fourier.weightedOrderedIntegral m χ χ
        (Fourier.balancedCutoffAmplitude χ phase (rectangleIndicator a b) i j)) ξ)) := by
  apply weightedOrderedIntegral_fourier_limit hχ h m (pow_nonneg (zero_le_one.trans h.one_le_bound) m)
  · intro n
    exact Fourier.balancedCutoffAmplitude_contDiff hχ (contDiff_smoothRectangle (ε n) a b) phase i j
  · intro n v
    exact (Fourier.norm_balancedCutoffAmplitude_le h phase _ i j v).trans
      ((mul_le_mul_of_nonneg_left (norm_smoothRectangle_le_one (hε n) a b _ hab)
        (pow_nonneg (zero_le_one.trans h.one_le_bound) m)).trans_eq (mul_one _))
  · intro v
    exact (tendsto_smoothRectangle hε hlim a b hab ![v i, v j]).const_mul _

end WaveTurbulence.Incoh
