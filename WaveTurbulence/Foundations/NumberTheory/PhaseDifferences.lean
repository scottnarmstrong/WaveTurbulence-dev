/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Actual differenced phases in the A-process

Translation and subtraction commute with derivatives. The real mean-value
theorem transfers nonzero derivative bounds to a phase difference, with the
exact factor equal to the shift length. No exponent-pair class is defined.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The real finite difference appearing in the actual Weyl correlations. -/
@[expose] def phaseDifference (f : ℝ → ℝ) (h x : ℝ) : ℝ := f (x+h)-f x

/-- Derivative of an actual finite difference, with both evaluation points
explicit and no off-interval differentiability assumption. -/
theorem phaseDifference_hasDerivAt {f g : ℝ → ℝ} {h x : ℝ}
    (hx : HasDerivAt f (g x) x) (hxh : HasDerivAt f (g (x+h)) (x+h)) :
    HasDerivAt (phaseDifference f h) (phaseDifference g h x) x := by
  exact (hxh.comp_add_const x h).sub hx

/-- Higher derivatives commute with the finite difference whenever the
phase is smooth at both actual evaluation points. -/
theorem iteratedDeriv_phaseDifference {f : ℝ → ℝ} {h x : ℝ} (n : ℕ)
    (hx : ContDiffAt ℝ n f x) (hxh : ContDiffAt ℝ n f (x+h)) :
    iteratedDeriv n (phaseDifference f h) x = phaseDifference (iteratedDeriv n f) h x := by
  have hs : ContDiffAt ℝ n (fun y => f (y+h)) x :=
    hxh.comp x (contDiffAt_id.add contDiffAt_const)
  have he := iteratedDeriv_fun_sub hs hx
  rw [iteratedDeriv_comp_add_const] at he
  exact he

/-- The mean-value theorem transfers absolute derivative bounds to a
finite difference with the exact shift factor. No sign assumption is needed. -/
theorem abs_phaseDifference_bounds {f g : ℝ → ℝ} {x h lo hi : ℝ}
    (hh : 0 < h) (hc : ContinuousOn f (Set.Icc x (x+h)))
    (hd : ∀ y ∈ Set.Ioo x (x+h), HasDerivAt f (g y) y)
    (hb : ∀ y ∈ Set.Ioo x (x+h), lo ≤ |g y| ∧ |g y| ≤ hi) :
    lo*h ≤ |phaseDifference f h x| ∧ |phaseDifference f h x| ≤ hi*h := by
  obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope f g (by linarith only [hh]) hc hd
  have hdiff : phaseDifference f h x = g y*h := by
    have heh : x+h-x = h := by ring
    rw [heh] at he
    exact ((eq_div_iff hh.ne').mp he).symm
  rw [hdiff,abs_mul,abs_of_pos hh]
  exact ⟨mul_le_mul_of_nonneg_right (hb y hy).1 hh.le,
    mul_le_mul_of_nonneg_right (hb y hy).2 hh.le⟩

end WaveTurbulence.NumberTheory
