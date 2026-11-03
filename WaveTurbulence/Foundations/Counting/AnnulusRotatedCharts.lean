/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.AnnulusChartCounting
public import WaveTurbulence.Foundations.Counting.LatticeRotations
import Mathlib.Tactic

/-!
# The other three Cartesian annulus charts

Exact lattice rotations transfer the proved upper-chart estimate to the right,
lower and left charts, uniformly in both centers.
-/

public section

namespace WaveTurbulence.Counting

private theorem negated_sub_sq (x y : ℝ) : (-x- -y)^2 = (x-y)^2 := by ring
private theorem abs_negated_sub (x y : ℝ) : |-x- -y| = |x-y| := by
  rw [neg_sub_neg,abs_sub_comm]

/-- The optimized elementary estimate in the right chart. -/
theorem card_annulus_right_chart_le (s : Finset (Fin 2 → ℤ))
    {r rho c₀ c₁ d L : ℝ}
    (hr : 0 < r) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ r^3) (hscale : 1 ≤ r^3*rho)
    (hL : 0 ≤ L)
    (hchart : ∀ n ∈ s, r^3/4 ≤ (n 0:ℝ)-c₀)
    (hhorizontal : ∀ n ∈ s, |(n 1:ℝ)-c₁| ≤ 2*r^3)
    (hproj : ∀ n ∈ s, |(n 1:ℝ)-d| ≤ L)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-r^3| ≤ rho) :
    (s.card:ℝ) ≤ 160000*(1+L*rho+L/r)*Real.sqrt (r^3*rho) := by
  apply card_annulus_chart_le_optimized_map s latticeQuarterTurn
    (c₀ := -c₁) (c₁ := c₀) (d := -d) hr hrho hrhoQ hscale hL
  · intro n hn
    change r^3/4 ≤ (n 0:ℝ)-c₀
    exact hchart n hn
  · intro n hn
    change |((-(n 1):ℤ):ℝ)- -c₁| ≤ 2*r^3
    rw [Int.cast_neg,abs_negated_sub]
    exact hhorizontal n hn
  · intro n hn
    change |((-(n 1):ℤ):ℝ)- -d| ≤ L
    rw [Int.cast_neg,abs_negated_sub]
    exact hproj n hn
  · intro n hn
    change |Real.sqrt (((( -(n 1):ℤ):ℝ)- -c₁)^2+((n 0:ℝ)-c₀)^2)-r^3| ≤ rho
    rw [Int.cast_neg,negated_sub_sq,add_comm]
    exact hann n hn

/-- The optimized elementary estimate in the lower chart. -/
theorem card_annulus_lower_chart_le (s : Finset (Fin 2 → ℤ))
    {r rho c₀ c₁ d L : ℝ}
    (hr : 0 < r) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ r^3) (hscale : 1 ≤ r^3*rho)
    (hL : 0 ≤ L)
    (hchart : ∀ n ∈ s, r^3/4 ≤ c₁-(n 1:ℝ))
    (hhorizontal : ∀ n ∈ s, |(n 0:ℝ)-c₀| ≤ 2*r^3)
    (hproj : ∀ n ∈ s, |(n 0:ℝ)-d| ≤ L)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-r^3| ≤ rho) :
    (s.card:ℝ) ≤ 160000*(1+L*rho+L/r)*Real.sqrt (r^3*rho) := by
  apply card_annulus_chart_le_optimized_map s latticeHalfTurn
    (c₀ := -c₀) (c₁ := -c₁) (d := -d) hr hrho hrhoQ hscale hL
  · intro n hn
    change r^3/4 ≤ ((-(n 1):ℤ):ℝ)- -c₁
    rw [Int.cast_neg,neg_sub_neg]
    exact hchart n hn
  · intro n hn
    change |((-(n 0):ℤ):ℝ)- -c₀| ≤ 2*r^3
    rw [Int.cast_neg,abs_negated_sub]
    exact hhorizontal n hn
  · intro n hn
    change |((-(n 0):ℤ):ℝ)- -d| ≤ L
    rw [Int.cast_neg,abs_negated_sub]
    exact hproj n hn
  · intro n hn
    change |Real.sqrt ((((-(n 0):ℤ):ℝ)- -c₀)^2+(((-(n 1):ℤ):ℝ)- -c₁)^2)-r^3| ≤ rho
    rw [Int.cast_neg,Int.cast_neg,negated_sub_sq,negated_sub_sq]
    exact hann n hn

/-- The optimized elementary estimate in the left chart. -/
theorem card_annulus_left_chart_le (s : Finset (Fin 2 → ℤ))
    {r rho c₀ c₁ d L : ℝ}
    (hr : 0 < r) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ r^3) (hscale : 1 ≤ r^3*rho)
    (hL : 0 ≤ L)
    (hchart : ∀ n ∈ s, r^3/4 ≤ c₀-(n 0:ℝ))
    (hhorizontal : ∀ n ∈ s, |(n 1:ℝ)-c₁| ≤ 2*r^3)
    (hproj : ∀ n ∈ s, |(n 1:ℝ)-d| ≤ L)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-r^3| ≤ rho) :
    (s.card:ℝ) ≤ 160000*(1+L*rho+L/r)*Real.sqrt (r^3*rho) := by
  apply card_annulus_chart_le_optimized_map s latticeThreeQuarterTurn
    (c₀ := c₁) (c₁ := -c₀) (d := d) hr hrho hrhoQ hscale hL
  · intro n hn
    change r^3/4 ≤ ((-(n 0):ℤ):ℝ)- -c₀
    rw [Int.cast_neg,neg_sub_neg]
    exact hchart n hn
  · intro n hn
    change |(n 1:ℝ)-c₁| ≤ 2*r^3
    exact hhorizontal n hn
  · intro n hn
    change |(n 1:ℝ)-d| ≤ L
    exact hproj n hn
  · intro n hn
    change |Real.sqrt (((n 1:ℝ)-c₁)^2+(((-(n 0):ℤ):ℝ)- -c₀)^2)-r^3| ≤ rho
    rw [Int.cast_neg,negated_sub_sq,add_comm]
    exact hann n hn

end WaveTurbulence.Counting
