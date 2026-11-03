/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.PairedHarmonic
public import WaveTurbulence.Foundations.VdCB.Phase
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Integrating the sharp sawtooth Fourier limit

The Fourier series converges off the integer lattice. Its endpoint
exception is a null set, and the uniform symmetric bound permits dominated
convergence against the derivative in Euler summation.
-/

public section

open MeasureTheory Filter Set
open scoped Topology
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

theorem norm_sawtoothRem_le_seven_halves (K : ℕ) (x : ℝ) : ‖sawtoothRem K x‖ ≤ 7 / 2 := by
  have hs : ‖(sawtooth x : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_sawtooth_le_half x
  have hF := norm_sawtoothFourier_le_three K x
  unfold sawtoothRem
  exact (norm_sub_le _ _).trans (by linarith only [hs, hF])

/-- Pointwise Fourier remainder convergence away from integer arguments. -/
theorem tendsto_sawtoothRem_zero {x : ℝ} (hx : integerDistance x 0 ≠ 0) :
    Tendsto (fun K : ℕ => sawtoothRem K x) atTop (𝓝 0) := by
  have hlim : Tendsto (fun K : ℕ => (Real.pi * ((K : ℝ) + 1) * integerDistance x 0)⁻¹)
      atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun K : ℕ => 1 / ((K : ℝ) + 1)) atTop (𝓝 0)).const_mul
        (Real.pi * integerDistance x 0)⁻¹
    convert hh using 1
    · funext K
      simp only [one_div, mul_inv]
      ring
    · simp only [mul_zero]
  exact squeeze_zero_norm (fun K => norm_sawtoothRem_le_dist K hx) hlim

/-- The exceptional integer lattice has Lebesgue measure zero. -/
theorem ae_integerDistance_ne_zero : ∀ᵐ x : ℝ ∂volume, integerDistance x 0 ≠ 0 := by
  filter_upwards [(Set.countable_range (fun n : ℤ => (n : ℝ))).ae_notMem volume] with x hx
  intro hz
  obtain ⟨n, hn⟩ := (integerDistance_eq_zero_iff x 0).mp hz
  exact hx ⟨n, by simpa only [sub_zero] using hn.symm⟩

private theorem continuous_sawtoothFourier (K : ℕ) : Continuous (sawtoothFourier K) := by
  unfold sawtoothFourier
  apply Continuous.neg
  apply continuous_finsetSum
  intro m hm
  exact (((contDiff_expPhase 0).continuous.comp (continuous_const.mul continuous_id)).div_const _)

private theorem measurable_sawtoothRem (K : ℕ) : Measurable (sawtoothRem K) := by
  have hs : Measurable (fun x : ℝ => (sawtooth x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (measurable_fract.sub_const (1 / 2))
  exact hs.sub (continuous_sawtoothFourier K).measurable

/-- The Fourier remainder in Euler summation vanishes after integration.
No pointwise assertion is made at the integer endpoints. -/
theorem tendsto_integral_sawtoothRem_mul_deriv {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F) (a b : ℝ) :
    Tendsto (fun K : ℕ => ∫ x in a..b, sawtoothRem K x * deriv F x) atTop (𝓝 0) := by
  have hm : ∀ᶠ K : ℕ in atTop,
      AEStronglyMeasurable (fun x => sawtoothRem K x * deriv F x) (volume.restrict (uIoc a b)) :=
    Filter.Eventually.of_forall fun K =>
      (measurable_sawtoothRem K).aestronglyMeasurable.mul hF.continuous_deriv_one.aestronglyMeasurable
  have hb : ∀ᶠ K : ℕ in atTop, ∀ᵐ x : ℝ ∂volume, x ∈ uIoc a b →
      ‖sawtoothRem K x * deriv F x‖ ≤ (7 / 2 : ℝ) * ‖deriv F x‖ :=
    Filter.Eventually.of_forall fun K => Filter.Eventually.of_forall fun x _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_sawtoothRem_le_seven_halves K x) (norm_nonneg _)
  have hi : IntervalIntegrable (fun x => (7 / 2 : ℝ) * ‖deriv F x‖) volume a b :=
    (hF.continuous_deriv_one.norm.const_mul _).intervalIntegrable a b
  have hl : ∀ᵐ x : ℝ ∂volume, x ∈ uIoc a b →
      Tendsto (fun K : ℕ => sawtoothRem K x * deriv F x) atTop (𝓝 (0 : ℂ)) := by
    filter_upwards [ae_integerDistance_ne_zero] with x hx _
    simpa only [zero_mul] using (tendsto_sawtoothRem_zero hx).mul_const (deriv F x)
  simpa only [intervalIntegral.integral_zero] using
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (f := fun _ : ℝ => (0 : ℂ)) (fun x => (7 / 2 : ℝ) * ‖deriv F x‖) hm hb hi hl

end WaveTurbulence.VdCB
