/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.Phase
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Logarithmic integration of the nonstationary kernel

The two ends of the normalized derivative range give logarithmic
primitives. This is the source of the logarithm in sharp truncated
Poisson summation.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.VdCB

/-- Exact logarithmic primitive for the two-sided derivative-range
kernel, with actual phase-coordinate derivative. -/
theorem integral_deriv_mul_reciprocal_kernel {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {a b N : ℝ} (hab : a ≤ b)
    (hrange : ∀ x ∈ Icc a b, 0 ≤ g x ∧ g x ≤ N) :
    (∫ x in a..b, deriv g x * (1 / (g x + 1) + 1 / (N + 1 - g x))) =
      (Real.log (g b + 1) - Real.log (N + 1 - g b)) -
        (Real.log (g a + 1) - Real.log (N + 1 - g a)) := by
  have hp (x : ℝ) (hx : x ∈ uIcc a b) : 0 < g x + 1 ∧ 0 < N + 1 - g x := by
    rw [uIcc_of_le hab] at hx
    obtain ⟨h0, hN⟩ := hrange x hx
    constructor <;> linarith
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun y => Real.log (g y + 1) - Real.log (N + 1 - g y))
        (deriv g x * (1 / (g x + 1) + 1 / (N + 1 - g x))) x := by
    have hh := (hg.differentiable (by norm_num) x).hasDerivAt
    have h1 := (hh.add_const 1).log (hp x hx).1.ne'
    have h2 := (hh.const_sub (N + 1)).log (hp x hx).2.ne'
    convert h1.sub h2 using 1; ring
  have hc : ContinuousOn (fun x => deriv g x * (1 / (g x + 1) + 1 / (N + 1 - g x))) (uIcc a b) := by
    apply hg.continuous_deriv_one.continuousOn.mul
    exact (continuousOn_const.div (hg.continuous.continuousOn.add continuousOn_const)
      (fun x hx => (hp x hx).1.ne')).add
      (continuousOn_const.div (continuousOn_const.sub hg.continuous.continuousOn)
        (fun x hx => (hp x hx).2.ne'))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))

/-- The kernel integral is bounded solely by the width of the derivative
range. No interval length occurs in this bound. -/
theorem integral_deriv_mul_reciprocal_kernel_le {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {a b N : ℝ} (hab : a ≤ b)
    (hrange : ∀ x ∈ Icc a b, 0 ≤ g x ∧ g x ≤ N) :
    (∫ x in a..b, deriv g x * (1 / (g x + 1) + 1 / (N + 1 - g x))) ≤ 2 * Real.log (N + 1) := by
  rw [integral_deriv_mul_reciprocal_kernel hg hab hrange]
  obtain ⟨ha0, haN⟩ := hrange a (left_mem_Icc.mpr hab)
  obtain ⟨hb0, hbN⟩ := hrange b (right_mem_Icc.mpr hab)
  have h1 : Real.log (g b + 1) ≤ Real.log (N + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 : 0 ≤ Real.log (N + 1 - g b) := Real.log_nonneg (by linarith)
  have h3 : 0 ≤ Real.log (g a + 1) := Real.log_nonneg (by linarith)
  have h4 : Real.log (N + 1 - g a) ≤ Real.log (N + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith only [h1, h2, h3, h4]

end WaveTurbulence.VdCB
