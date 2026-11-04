/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.GevreyEnvelope

/-! # Pointwise domination by the common Gevrey frequency envelope -/

public section
namespace WaveTurbulence.RegAsymp
open scoped ENNReal

/-- Every derivative-order contribution is bounded by its factorial times
the SAME envelope. No dimension- or order-dependent choice of frequency
majorant is made. This remains true at an infinite envelope. -/
theorem gevrey_envelope_dominates {Λ : Type*} (G : ℕ → Λ → ℝ≥0∞) (k : ℕ) (ω : Λ) :
    G k ω ≤ ENNReal.ofReal ((4*k).factorial : ℝ) *
      ∑' j : ℕ, ENNReal.ofReal (1 / ((4*j).factorial : ℝ)) * G j ω := by
  have hp : (0 : ℝ) < (4*k).factorial := by positivity
  have hc : ENNReal.ofReal ((4*k).factorial : ℝ) *
      ENNReal.ofReal (1 / ((4*k).factorial : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul hp.le]
    rw [mul_one_div_cancel hp.ne']
    exact ENNReal.ofReal_one
  calc G k ω = (ENNReal.ofReal ((4*k).factorial : ℝ) *
      ENNReal.ofReal (1 / ((4*k).factorial : ℝ))) * G k ω := by rw [hc,one_mul]
    _ = ENNReal.ofReal ((4*k).factorial : ℝ) *
      (ENNReal.ofReal (1 / ((4*k).factorial : ℝ)) * G k ω) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_right (ENNReal.le_tsum (f := fun j : ℕ =>
      ENNReal.ofReal (1 / ((4*j).factorial : ℝ)) * G j ω) k) _

end WaveTurbulence.RegAsymp
