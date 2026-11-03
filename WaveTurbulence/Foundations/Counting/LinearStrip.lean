/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.QuadraticStrip
import Mathlib.Tactic

/-!
# Integer points in one-dimensional linear strips

Uniform interval counts for the coefficient summation in DH23 `estcross`.
-/

public section

namespace WaveTurbulence.Counting

/-- Integer samples satisfying a linear strip condition occupy an interval
of length at most `2*rho/abs a`. -/
theorem card_linear_strip_le (s : Finset ℤ) {a b rho : ℝ}
    (ha : a ≠ 0) (hrho : 0 ≤ rho)
    (h : ∀ n ∈ s, |a*(n:ℝ)-b| ≤ rho) :
    (s.card:ℝ) ≤ 2*rho/|a|+1 := by
  have hap : 0 < |a| := abs_pos.mpr ha
  apply card_int_finset_le_of_diameter s (by positivity)
  intro x hx y hy
  apply (le_div_iff₀ hap).mpr
  have hx' := abs_le.mp (h x hx)
  have hy' := abs_le.mp (h y hy)
  have hb : |a*((x:ℝ)-y)| ≤ 2*rho := by
    apply abs_le.mpr
    constructor <;> linarith only [hx'.1,hx'.2,hy'.1,hy'.2]
  rw [abs_mul] at hb
  nlinarith only [hb]

/-- When the strip width dominates the coefficient, absorb the endpoint
constant into the geometric interval length. -/
theorem card_linear_strip_le_of_abs_le (s : Finset ℤ) {a b rho : ℝ}
    (ha : a ≠ 0) (hrho : 0 ≤ rho) (habs : |a| ≤ rho)
    (h : ∀ n ∈ s, |a*(n:ℝ)-b| ≤ rho) :
    (s.card:ℝ) ≤ 3*rho/|a| := by
  have hc := card_linear_strip_le s ha hrho h
  have h1 : 1 ≤ rho/|a| := (le_div_iff₀ (abs_pos.mpr ha)).mpr (by simpa only [one_mul] using habs)
  have h2 : 2*rho/|a| = 2*(rho/|a|) := by ring
  have h3 : 3*rho/|a| = 3*(rho/|a|) := by ring
  rw [h2] at hc
  rw [h3]
  linarith only [hc,h1]

end WaveTurbulence.Counting
