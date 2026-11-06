/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
/-! The counting/Fourier separation in TARGET redvine5, with extended cardinalities and no finiteness assumption. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set
open scoped ENNReal

theorem tsum_le_fiber_count_mul {X J : Type*} (π : X → J) (f : X → ℝ≥0∞)
    (B : J → ℝ≥0∞) (E : ℝ≥0∞)
    (hcount : ∀ j, ((π ⁻¹' {j}).encard : ℝ≥0∞) ≤ E)
    (hbound : ∀ x, f x ≤ B (π x)) :
    (∑' x, f x) ≤ E * ∑' j, B j := by
  rw [← ENNReal.tsum_fiberwise f π, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  calc
    (∑' x : π ⁻¹' {j}, f x.1) ≤ ∑' _x : π ⁻¹' {j}, B j := by
      apply ENNReal.tsum_le_tsum
      intro x
      have he : π x.1 = j := x.2
      simpa only [he] using hbound x.1
    _ = ((π ⁻¹' {j}).encard : ℝ≥0∞) * B j  := ENNReal.tsum_set_const _ _
    _ ≤ E * B j := mul_le_mul_of_nonneg_right (hcount j) (by positivity)

end WaveTurbulence.LGSpine
