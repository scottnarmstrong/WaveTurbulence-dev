/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.Statement
import Mathlib.Tactic

/-! # The dimensional margin in the exceptional Wick-factor contribution

DH23 end of the proof of Prop6.1; DH21 end of Prop6.7. Fixing one
x-variable to zero loses one lattice pair and leaves one free y-variable.
Its relative power is L^(-(d-2gamma)), uniformly stronger than L^(-gamma1).
-/

public section
namespace WaveTurbulence.RegAsymp

/-- The zero-coordinate contribution has a uniform half-power margin
beyond the required gamma1 gain, in every dimension d≥3. -/
theorem wick_dimension_margin {d : ℕ} (hd : 3 ≤ d) (γ : ℝ) :
    ApproxNT.gamma1 d γ + 1 / 2 ≤ (d : ℝ) - 2 * γ := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : ApproxNT.gamma1 d γ ≤ 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h2 : ApproxNT.gamma1 d γ ≤ 2 * ((d : ℝ)-1) * (1-γ) :=
    (min_le_right _ _).trans (min_le_right _ _)
  by_cases hc : γ ≤ 3 / 4
  · linarith only [h1,hd',hc]
  · have hcross : 0 ≤ ((d : ℝ)-3) * (2*γ-1) := mul_nonneg (by linarith) (by linarith)
    nlinarith only [h2,hcross,hc]

end WaveTurbulence.RegAsymp
