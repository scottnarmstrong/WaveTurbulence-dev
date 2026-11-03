/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Selecting interior critical frequencies and endpoint guards

Actual upper curvature bounds place all frequencies without an interior
critical point into endpoint guard intervals or separated regions. The
interior critical points themselves follow from the intermediate value
theorem applied to the actual derivative.
-/

public section

open Set

namespace WaveTurbulence.NumberTheory

/-- Every frequency between the two inner endpoint derivatives has an
actual critical point a full radius away from both original endpoints. -/
theorem exists_interior_critical_point_of_frequency_bounds {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b r nu : ℝ} (_hr : 0 < r) (hwidth : 2*r ≤ b-a)
    (hnu : deriv f (a+r) ≤ nu ∧ nu ≤ deriv f (b-r)) :
    ∃ c ∈ Icc (a+r) (b-r), deriv f c = nu := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hab : a+r ≤ b-r := by linarith only [hwidth]
  have hh := intermediate_value_Icc hab hf1.continuous.continuousOn hnu
  obtain ⟨c,hc,he⟩ := hh
  exact ⟨c,hc,he⟩

/-- Away from the two endpoint guard intervals, every frequency outside
the interior stationary range is uniformly separated on the whole interval. -/
theorem frequency_outside_stationary_and_guards_separated {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b r Lam nu : ℝ} (hr : 0 < r) (hwidth : 2*r ≤ b-a)
    (hcurv : ∀ x ∈ Icc a b, 0 ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ Lam)
    (houtside : ¬ (deriv f (a+r) ≤ nu ∧ nu ≤ deriv f (b-r)))
    (hga : Lam*r < |nu-deriv f a|) (hgb : Lam*r < |nu-deriv f b|) :
    (∀ x ∈ Icc a b, deriv f x ≤ nu-Lam*r) ∨
      (∀ x ∈ Icc a b, nu+Lam*r ≤ deriv f x) := by
  have hab : a ≤ b := by linarith only [hr,hwidth]
  have ha : a ∈ Icc a b := ⟨le_rfl,hab⟩
  have hb : b ∈ Icc a b := ⟨hab,le_rfl⟩
  have har : a+r ∈ Icc a b := ⟨by linarith only [hr],by linarith only [hr,hwidth]⟩
  have hbr : b-r ∈ Icc a b := ⟨by linarith only [hr,hwidth],by linarith only [hr]⟩
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hlow := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hf1.continuous.continuousOn (hf1.differentiable (by norm_num)).differentiableOn
    (fun x hx => (hcurv x (interior_subset hx)).1)
  have hhigh := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    hf1.continuous.continuousOn (hf1.differentiable (by norm_num)).differentiableOn
    (fun x hx => (hcurv x (interior_subset hx)).2)
  have hleft := hhigh a ha (a+r) har (by linarith only [hr])
  have hright := hhigh (b-r) hbr b hb (by linarith only [hr])
  by_cases hlo : nu < deriv f (a+r)
  · right
    have hsep : nu+Lam*r ≤ deriv f a := by
      rcases (lt_abs.mp hga) with hpos | hneg
      · linarith only [hpos,hleft,hlo]
      · linarith only [hneg]
    intro x hx
    have hxlo := hlow a ha x hx hx.1
    linarith only [hsep,hxlo]
  · have hhi : deriv f (b-r) < nu := by
      by_contra hn
      exact houtside ⟨le_of_not_gt hlo,le_of_not_gt hn⟩
    left
    have hsep : deriv f b ≤ nu-Lam*r := by
      rcases (lt_abs.mp hgb) with hpos | hneg
      · linarith only [hpos]
      · linarith only [hneg,hright,hhi]
    intro x hx
    have hxhi := hlow x hx b hb hx.2
    linarith only [hsep,hxhi]

end WaveTurbulence.NumberTheory
