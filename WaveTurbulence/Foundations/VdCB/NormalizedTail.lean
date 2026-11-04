/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.FiniteFrequencyTail
public import WaveTurbulence.Foundations.VdCB.OuterFrequencies
public import WaveTurbulence.Foundations.VdCB.LogKernel

/-!
# Quantitative tails outside the derivative range

This is the logarithmic nonstationary estimate for sharp Poisson summation
on integer endpoints. Equal cutoffs are used at the two ends of the
normalized frequency interval `[0,N]`.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The outer frequency tail is bounded independently of its cutoff.
The hypotheses concern actual first and second derivatives only. -/
theorem norm_sum_outerFrequencies_integral_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (a b : ℤ) (hab : a ≤ b) (N K : ℕ)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hsecond : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv (deriv f) x) :
    ‖∑ ν ∈ outerFrequencies N K, ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)‖ ≤
      (2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hne (ν : ℤ) (hν : ν ∈ outerFrequencies N K) (x : ℝ) (hx : x ∈ uIcc (a : ℝ) b) :
      deriv f x - ν ≠ 0 := by
    rw [uIcc_of_le habR] at hx
    exact sub_ne_zero_of_mem_outerFrequencies (hrange x hx).1 (hrange x hx).2 hν
  have hiν (ν : ℤ) (hν : ν ∈ outerFrequencies N K) :
      IntervalIntegrable (fun x => |deriv (deriv f) x| * ((deriv f x - ν) ^ 2)⁻¹)
        volume (a : ℝ) b := by
    apply ContinuousOn.intervalIntegrable (μ := volume)
    exact hf1.continuous_deriv_one.abs.continuousOn.mul
      (((hf1.continuous.continuousOn.sub continuousOn_const).pow 2).inv₀
        (fun x hx => pow_ne_zero 2 (hne ν hν x hx)))
  have hi : IntervalIntegrable (fun x => |deriv (deriv f) x| *
      ∑ ν ∈ outerFrequencies N K, ((deriv f x - ν) ^ 2)⁻¹) volume (a : ℝ) b := by
    simp_rw [Finset.mul_sum]
    convert IntervalIntegrable.sum _ hiν using 1
    funext x
    rw [Finset.sum_apply]
  have hp (x : ℝ) (hx : x ∈ uIcc (a : ℝ) b) :
      0 < deriv f x + 1 ∧ 0 < (N : ℝ) + 1 - deriv f x := by
    rw [uIcc_of_le habR] at hx
    obtain ⟨h0, hN⟩ := hrange x hx
    constructor <;> linarith
  have hc : ContinuousOn (fun x => deriv (deriv f) x *
      (1 / (deriv f x + 1) + 1 / ((N : ℝ) + 1 - deriv f x))) (uIcc (a : ℝ) b) := by
    apply hf1.continuous_deriv_one.continuousOn.mul
    exact (continuousOn_const.div (hf1.continuous.continuousOn.add continuousOn_const)
      (fun x hx => (hp x hx).1.ne')).add
      (continuousOn_const.div (continuousOn_const.sub hf1.continuous.continuousOn)
        (fun x hx => (hp x hx).2.ne'))
  have hrem : (∫ x in (a : ℝ)..b, |deriv (deriv f) x| *
      ∑ ν ∈ outerFrequencies N K, ((deriv f x - ν) ^ 2)⁻¹) ≤
        4 * Real.log ((N : ℝ) + 1) := by
    calc
      _ ≤ ∫ x in (a : ℝ)..b, 2 * (deriv (deriv f) x *
          (1 / (deriv f x + 1) + 1 / ((N : ℝ) + 1 - deriv f x))) := by
        apply intervalIntegral.integral_mono_on habR hi
          ((hc.const_mul 2).intervalIntegrable (μ := volume))
        intro x hx
        rw [abs_of_nonneg (hsecond x hx)]
        have hh := mul_le_mul_of_nonneg_left
          (sum_outerFrequencies_inv_sq_le (N := N) (K := K) (hrange x hx).1 (hrange x hx).2)
          (hsecond x hx)
        convert hh using 1; ring
      _ = 2 * ∫ x in (a : ℝ)..b, deriv (deriv f) x *
          (1 / (deriv f x + 1) + 1 / ((N : ℝ) + 1 - deriv f x)) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ 2 * (2 * Real.log ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left
          (integral_deriv_mul_reciprocal_kernel_le hf1 habR hrange) (by norm_num)
      _ = _ := by ring
  apply (norm_sum_integral_expPhase_sub_frequency_le hf a b hab (outerFrequencies N K) hne).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hb := abs_sum_outerFrequencies_inv_le (K := K)
    (hrange b (right_mem_Icc.mpr habR)).1 (hrange b (right_mem_Icc.mpr habR)).2
  have ha := abs_sum_outerFrequencies_inv_le (K := K)
    (hrange a (left_mem_Icc.mpr habR)).1 (hrange a (left_mem_Icc.mpr habR)).2
  linarith only [hb, ha, hrem]

end WaveTurbulence.VdCB
