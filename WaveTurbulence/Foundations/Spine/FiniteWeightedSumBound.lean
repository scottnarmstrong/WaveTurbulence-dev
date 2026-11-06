/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.Complex.Basic
/-! Explicit weighted enumeration budgets for a finite source-choice partition. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

/-- Normalize each source piece before summing; the combinatorial budget remains visible. -/
theorem norm_sum_le_of_weighted_bounds {J : Type*} [Fintype J] (K : J → ℂ)
    (cost : J → ℝ) (B : ℝ) (hcost : ∀ j, 0 < cost j)
    (hb : ∀ j, ‖K j‖ * cost j ≤ B) :
    ‖∑ j, K j‖ ≤ B * ∑ j, (cost j)⁻¹ := by
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  have h := (le_div_iff₀ (hcost j)).mpr (hb j)
  simpa only [div_eq_mul_inv] using h

end WaveTurbulence.LGSpine
