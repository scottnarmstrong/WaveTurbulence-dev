/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.EulerSummation
public import WaveTurbulence.Foundations.VdCB.SawtoothLimit
public import WaveTurbulence.Foundations.VdCB.SymmetricKernel

/-!
# Sharp Poisson summation as a symmetric limit

The finite Fourier primitive and Euler summation prove the exact midpoint
Poisson limit for C¹ functions. The half-open sum has the explicit
`(F(b)-F(a))/2` correction. A quantitative truncation to the derivative
range is a separate tail estimate.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

private theorem continuous_symmetricKernel (K : ℕ) : Continuous (symmetricKernel K) := by
  unfold symmetricKernel
  apply continuous_finsetSum
  intro m hm
  exact (contDiff_expPhase 0).continuous.comp (continuous_const.mul continuous_id)

private theorem continuous_fourierPrimitive (K : ℕ) : Continuous (sawtoothFourier K) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_sawtoothFourier K x).continuousAt

/-- A finite integration-by-parts identity for the actual sharp kernel. -/
theorem integral_add_fourierPrimitive_mul_deriv {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F)
    (K : ℕ) (a b : ℕ) :
    (∫ x in (a : ℝ)..(b : ℝ), F x) +
      (∫ x in (a : ℝ)..(b : ℝ), sawtoothFourier K x * deriv F x) =
        ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ∫ x in (a : ℝ)..(b : ℝ), expPhase ((m : ℝ) * x) * F x := by
  have hc := continuous_symmetricKernel K
  have hp := continuous_fourierPrimitive K
  have hd : Continuous (fun x => 1 - symmetricKernel K x) := continuous_const.sub hc
  have hFi := hF.continuous.intervalIntegrable (μ := volume) (a : ℝ) (b : ℝ)
  have hDi := (hc.mul hF.continuous).intervalIntegrable (μ := volume) (a : ℝ) (b : ℝ)
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hp.continuousOn hF.continuous.continuousOn
    (fun x _ => hasDerivAt_sawtoothFourier K x)
    (fun x _ => (hF.differentiable (by norm_num) x).hasDerivAt)
    (hd.intervalIntegrable (μ := volume) (a : ℝ) (b : ℝ))
    (hF.continuous_deriv_one.intervalIntegrable (μ := volume) (a : ℝ) (b : ℝ))
  have ha := sawtoothFourier_intCast K (a : ℤ)
  have hb := sawtoothFourier_intCast K (b : ℤ)
  simp only [Int.cast_natCast] at ha hb
  rw [ha, hb, zero_mul, zero_mul, sub_self, zero_sub] at hh
  have hi : (∫ x in (a : ℝ)..(b : ℝ), (1 - symmetricKernel K x) * F x) =
      (∫ x in (a : ℝ)..(b : ℝ), F x) - ∫ x in (a : ℝ)..(b : ℝ), symmetricKernel K x * F x := by
    simp_rw [sub_mul, one_mul]
    exact intervalIntegral.integral_sub hFi hDi
  rw [hi] at hh
  have heq : (∫ x in (a : ℝ)..(b : ℝ), symmetricKernel K x * F x) =
      ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∫ x in (a : ℝ)..(b : ℝ), expPhase ((m : ℝ) * x) * F x := by
    simp_rw [symmetricKernel, Finset.sum_mul]
    apply intervalIntegral.integral_finsetSum
    intro m hm
    exact (((contDiff_expPhase 0).continuous.comp (continuous_const.mul continuous_id)).mul hF.continuous).intervalIntegrable _ _
  rw [← heq]
  linear_combination hh

/-- Sharp Poisson summation with midpoint endpoints, proved from the
symmetric Fourier limit rather than assumed absolute summability. -/
theorem poisson_symmetric_limit {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F) {a b : ℕ} (hab : a ≤ b) :
    Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ∫ x in (a : ℝ)..(b : ℝ), expPhase ((m : ℝ) * x) * F x) atTop
      (𝓝 ((∑ n ∈ Finset.Ico a b, F ((n : ℝ) + 1)) - (F b - F a) / 2)) := by
  have hψ := intervalIntegrable_sawtooth_mul_deriv hF hab
  have hp (K : ℕ) := ((continuous_fourierPrimitive K).mul hF.continuous_deriv_one).intervalIntegrable
    (μ := volume) (a : ℝ) (b : ℝ)
  have hR (K : ℕ) : IntervalIntegrable (fun x => sawtoothRem K x * deriv F x) volume (a : ℝ) (b : ℝ) := by
    convert hψ.sub (hp K) using 1
    funext x
    unfold sawtoothRem
    simp only [Pi.mul_apply]
    ring
  have heq (K : ℕ) : (∫ x in (a : ℝ)..(b : ℝ), sawtoothFourier K x * deriv F x) =
      (∫ x in (a : ℝ)..(b : ℝ), (sawtooth x : ℂ) * deriv F x) -
        ∫ x in (a : ℝ)..(b : ℝ), sawtoothRem K x * deriv F x := by
    rw [← intervalIntegral.integral_sub hψ (hR K)]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    unfold sawtoothRem
    ring
  let C : ℂ := (∫ x in (a : ℝ)..(b : ℝ), F x) +
    ∫ x in (a : ℝ)..(b : ℝ), (sawtooth x : ℂ) * deriv F x
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).sub
    (tendsto_integral_sawtoothRem_mul_deriv hF (a : ℝ) (b : ℝ))
  convert hlim using 1
  · funext K
    rw [← integral_add_fourierPrimitive_mul_deriv hF, heq]
    dsimp only [C]
    ring
  · rw [euler_summation hF hab]
    dsimp only [C]
    simp only [sub_zero]
    congr 1
    ring

end WaveTurbulence.VdCB
