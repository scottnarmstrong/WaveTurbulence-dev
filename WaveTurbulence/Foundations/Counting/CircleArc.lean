/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import WaveTurbulence.Foundations.NumberTheory.DerivativeTests
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
# Derivatives of circular arcs

Local analytic ingredients for NT-CIRCLE-v2 goal 2. The arc is defined by
the actual square-root formula, with derivative identities inside the circle.
No lattice count or discrepancy bound is encoded in the definitions.
-/

public section

namespace WaveTurbulence.Counting

/-- The nonnegative height of the circle above horizontal coordinate `x`. -/
@[expose] noncomputable def circleHeight (R c x : ℝ) : ℝ :=
  Real.sqrt (R ^ 2 - (x - c) ^ 2)

theorem circleHeight_pos {R c x : ℝ} (h : (x - c) ^ 2 < R ^ 2) :
    0 < circleHeight R c x := Real.sqrt_pos.mpr (sub_pos.mpr h)

theorem circleHeight_sq {R c x : ℝ} (h : (x - c) ^ 2 ≤ R ^ 2) :
    circleHeight R c x ^ 2 = R ^ 2 - (x - c) ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr h)

/-- The first derivative on the open circular arc. -/
theorem circleHeight_hasDerivAt {R c x : ℝ} (h : (x - c) ^ 2 < R ^ 2) :
    HasDerivAt (circleHeight R c) (-(x - c) / circleHeight R c x) x := by
  have hbase : HasDerivAt (fun y : ℝ => y - c) 1 x :=
    (hasDerivAt_id x).sub_const c
  have hsquare : HasDerivAt (fun y : ℝ => (y - c) ^ 2) (2 * (x - c)) x := by
    simpa only [Function.comp_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one] using!
      (hasDerivAt_pow 2 (x - c)).comp x hbase
  have hpoly : HasDerivAt (fun y : ℝ => R ^ 2 - (y - c) ^ 2) (-2 * (x - c)) x := by
    simpa only [neg_mul] using hsquare.const_sub (R ^ 2)
  have hs := hpoly.sqrt (ne_of_gt (sub_pos.mpr h))
  change HasDerivAt (circleHeight R c) (-2 * (x - c) / (2 * circleHeight R c x)) x at hs
  have heq : -2 * (x - c) / (2 * circleHeight R c x) = -(x - c) / circleHeight R c x := by
    ring
  rw [heq] at hs
  exact hs

private theorem circle_second_derivative_algebra {R u s : ℝ} (hs : s ≠ 0)
    (heq : s ^ 2 = R ^ 2 - u ^ 2) :
    ((-1) * s - (-u) * (-u / s)) / s ^ 2 = -(R ^ 2) / s ^ 3 := by
  field_simp
  nlinarith only [heq]

/-- The second derivative is negative and has size `R² / height³`. -/
theorem circleHeight_first_hasDerivAt {R c x : ℝ} (h : (x - c) ^ 2 < R ^ 2) :
    HasDerivAt (fun y => -(y - c) / circleHeight R c y)
      (-(R ^ 2) / circleHeight R c x ^ 3) x := by
  have hs : circleHeight R c x ≠ 0 := (circleHeight_pos h).ne'
  have hbase : HasDerivAt (fun y : ℝ => y - c) 1 x :=
    (hasDerivAt_id x).sub_const c
  have hnum : HasDerivAt (fun y : ℝ => -(y - c)) (-1) x := hbase.neg
  have hd := hnum.div (circleHeight_hasDerivAt h) hs
  rw [circle_second_derivative_algebra hs (circleHeight_sq h.le)] at hd
  exact hd

/-- On a height block `[H,2H]`, the curvature lies in an interval of ratio eight. -/
theorem circleHeight_curvature_mem_Icc {R c x H : ℝ} (hH : 0 < H)
    (hlo : H ≤ circleHeight R c x) (hhi : circleHeight R c x ≤ 2 * H) :
    R ^ 2 / circleHeight R c x ^ 3 ∈
      Set.Icc (R ^ 2 / (8 * H ^ 3)) (8 * (R ^ 2 / (8 * H ^ 3))) := by
  have hs : 0 < circleHeight R c x := hH.trans_le hlo
  have hpowlo := pow_le_pow_left₀ hH.le hlo 3
  have hpowhi := pow_le_pow_left₀ hs.le hhi 3
  norm_num only [mul_pow, Nat.reducePow] at hpowhi
  constructor
  · exact div_le_div_of_nonneg_left (sq_nonneg R) (pow_pos hs 3) hpowhi
  · have heq : 8 * (R ^ 2 / (8 * H ^ 3)) = R ^ 2 / H ^ 3 := by ring
    rw [heq]
    exact div_le_div_of_nonneg_left (sq_nonneg R) (pow_pos hH 3) hpowlo

/-- An explicit exponential-sum bound on a circular arc whose heights stay
in `[H,2H]`. The horizontal shift `t`, circle center `c`, and vertical phase
shift `d` are arbitrary; all non-arithmetic hypotheses describe the geometry
of the actual arc, rather than an assumed exponential-sum bound. -/
theorem circle_arc_exp_sum_le {R c t d H u : ℝ} {a b : ℕ}
    (hab : a ≤ b) (hR : 0 < R) (hH : 0 < H) (hu : 0 < u)
    (hblock : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1),
      circleHeight R c (x + t) ∈ Set.Icc H (2 * H)) :
    ‖∑ n ∈ Finset.Ioc a b,
      NumberTheory.expPhase (u * circleHeight R c ((n : ℝ) + t) + d)‖ ≤
      8 * (8 * ((b : ℝ) - a) * Real.sqrt (u * (R ^ 2 / (8 * H ^ 3))) +
        1 / Real.sqrt (u * (R ^ 2 / (8 * H ^ 3)))) := by
  have hlam : 0 < u * (R ^ 2 / (8 * H ^ 3)) := by positivity
  have hinside (x : ℝ) (hx : x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1)) :
      (x + t - c) ^ 2 < R ^ 2 := by
    have hp : 0 < circleHeight R c (x + t) := hH.trans_le (hblock x hx).1
    have hdiff := Real.sqrt_pos.mp hp
    linarith only [hdiff]
  apply NumberTheory.van_der_corput_second_derivative_of_neg
    (f := fun x => u * circleHeight R c (x + t) + d)
    (f' := fun x => u * (-(x + t - c) / circleHeight R c (x + t)))
    (f'' := fun x => u * (-(R ^ 2) / circleHeight R c (x + t) ^ 3))
    hab hlam (by norm_num : (1 : ℝ) ≤ 8)
  · intro x hx
    exact (((circleHeight_hasDerivAt (hinside x hx)).comp_add_const x t).const_mul u).add_const d
  · intro x hx
    exact ((circleHeight_first_hasDerivAt (hinside x hx)).comp_add_const x t).const_mul u
  · intro x hx
    obtain ⟨hl, hh⟩ := circleHeight_curvature_mem_Icc hH (hblock x hx).1 (hblock x hx).2
    have hlo := mul_le_mul_of_nonneg_left hl hu.le
    have hhi := mul_le_mul_of_nonneg_left hh hu.le
    constructor <;> simp only [neg_div, mul_neg] <;> linarith only [hlo, hhi]

end WaveTurbulence.Counting
