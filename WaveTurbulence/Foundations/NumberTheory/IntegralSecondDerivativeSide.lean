/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VdCB.NonstationaryNegative
import Mathlib.Tactic

/-!
# One-sided second-derivative oscillatory integral bounds

A curvature lower bound makes the derivative grow at least linearly.
Removing one interval of length `1/sqrt(mu)` leaves a nonstationary tail.
The bounds include stationary points at either endpoint, without requiring
any distance of an endpoint derivative from an integer frequency.
-/

public section

namespace WaveTurbulence.NumberTheory

open MeasureTheory Set

/-- A nonnegative derivative at the left endpoint, with positive curvature,
gives a uniform square-root integral bound. -/
theorem norm_integral_expPhase_le_of_second_pos_left {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b mu : ℝ} (hab : a ≤ b) (hmu : 0 < mu)
    (ha : 0 ≤ deriv f a) (hcurv : ∀ x ∈ Icc a b, mu ≤ deriv (deriv f) x) :
    ‖∫ x in a..b, expPhase (f x)‖ ≤ 1/Real.sqrt mu+1/(Real.pi*Real.sqrt mu) := by
  let r : ℝ := 1/Real.sqrt mu
  have hs : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  have hr : 0 < r := by dsimp only [r]; positivity
  have hmr : mu*r = Real.sqrt mu := by dsimp only [r]; rw [mul_one_div,Real.div_sqrt]
  change _ ≤ r+1/(Real.pi*Real.sqrt mu)
  by_cases hshort : b ≤ a+r
  · have hh := VdCB.norm_integral_expPhase_le hab f
    have hp : 0 ≤ 1/(Real.pi*Real.sqrt mu) := by positivity
    linarith only [hh,hshort,hp]
  have hcut : a+r ≤ b := le_of_not_ge hshort
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hsec := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hf1.continuous.continuousOn (hf1.differentiable (by norm_num)).differentiableOn
    (fun x hx => hcurv x (interior_subset hx))
  have htail := VdCB.norm_integral_expPhase_le_of_deriv_pos hf hcut hs
    (fun x hx => by
      have hx' : x ∈ Icc a b := ⟨by linarith only [hx.1,hr],hx.2⟩
      have hh := hsec a ⟨le_rfl,hab⟩ x hx' hx'.1
      have hd := mul_le_mul_of_nonneg_left (show r ≤ x-a by linarith only [hx.1]) hmu.le
      rw [hmr] at hd
      linarith only [hh,hd,ha])
    (fun x hx => hmu.le.trans (hcurv x ⟨by linarith only [hx.1,hr],hx.2⟩))
  have hsmall : ‖∫ x in a..a+r, expPhase (f x)‖ ≤ r :=
    (VdCB.norm_integral_expPhase_le (by linarith only [hr]) f).trans_eq (by ring)
  have hc : Continuous (fun x => expPhase (f x)) := (VdCB.contDiff_expPhase 0).continuous.comp hf.continuous
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable a (a+r)) (hc.intervalIntegrable (a+r) b)
  rw [← he]
  exact (norm_add_le _ _).trans (add_le_add hsmall htail)

/-- The reflected endpoint convention for a nonpositive derivative at the
right endpoint and positive curvature. -/
theorem norm_integral_expPhase_le_of_second_pos_right {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b mu : ℝ} (hab : a ≤ b) (hmu : 0 < mu)
    (hb : deriv f b ≤ 0) (hcurv : ∀ x ∈ Icc a b, mu ≤ deriv (deriv f) x) :
    ‖∫ x in a..b, expPhase (f x)‖ ≤ 1/Real.sqrt mu+1/(Real.pi*Real.sqrt mu) := by
  let r : ℝ := 1/Real.sqrt mu
  have hs : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  have hr : 0 < r := by dsimp only [r]; positivity
  have hmr : mu*r = Real.sqrt mu := by dsimp only [r]; rw [mul_one_div,Real.div_sqrt]
  change _ ≤ r+1/(Real.pi*Real.sqrt mu)
  by_cases hshort : b-r ≤ a
  · have hh := VdCB.norm_integral_expPhase_le hab f
    have hp : 0 ≤ 1/(Real.pi*Real.sqrt mu) := by positivity
    linarith only [hh,hshort,hp]
  have hcut : a ≤ b-r := le_of_not_ge hshort
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hsec := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hf1.continuous.continuousOn (hf1.differentiable (by norm_num)).differentiableOn
    (fun x hx => hcurv x (interior_subset hx))
  have htail := VdCB.norm_integral_expPhase_le_of_deriv_neg hf hcut hs
    (fun x hx => by
      have hx' : x ∈ Icc a b := ⟨hx.1,by linarith only [hx.2,hr]⟩
      have hh := hsec x hx' b ⟨hab,le_rfl⟩ hx'.2
      have hd := mul_le_mul_of_nonneg_left (show r ≤ b-x by linarith only [hx.2]) hmu.le
      rw [hmr] at hd
      linarith only [hh,hd,hb])
    (fun x hx => hmu.le.trans (hcurv x ⟨hx.1,by linarith only [hx.2,hr]⟩))
  have hsmall : ‖∫ x in b-r..b, expPhase (f x)‖ ≤ r :=
    (VdCB.norm_integral_expPhase_le (by linarith only [hr]) f).trans_eq (by ring)
  have hc : Continuous (fun x => expPhase (f x)) := (VdCB.contDiff_expPhase 0).continuous.comp hf.continuous
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable a (b-r)) (hc.intervalIntegrable (b-r) b)
  rw [← he]
  exact (norm_add_le _ _).trans ((add_le_add htail hsmall).trans_eq (by ring))

end WaveTurbulence.NumberTheory
