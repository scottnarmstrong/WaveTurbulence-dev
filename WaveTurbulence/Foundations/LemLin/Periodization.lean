/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
# The mass of a lattice periodization

The one-period L¹ step in TARGET `lemlin`, L1541–L1543. Integrating the
periodized absolute Fourier transform over one frequency cell recovers its
whole-line mass. The nonnegative formulation allows Tonelli without imposing
pointwise convergence hypotheses on a periodized series.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set
open scoped ENNReal

/-- Translated cells of any positive length partition the whole-line integral. -/
theorem hasSum_integral_period_shifts {f : ℝ → ℝ} (hf : Integrable f)
    {L : ℝ} (hL : 0 < L) (τ : ℝ) :
    HasSum (fun n : ℤ => ∫ u in τ..τ + L, f (u + L * n)) (∫ u, f u) := by
  have hscaled : Integrable (fun x : ℝ => f (L * x + τ)) :=
    (hf.comp_add_right τ).comp_mul_left' hL.ne'
  have hs := (hscaled.hasSum_intervalIntegral 0).const_smul L
  have hi (n : ℤ) :
      L • (∫ x in (n : ℝ)..(n : ℝ) + 1, f (L * x + τ)) =
        ∫ u in τ..τ + L, f (u + L * n) := by
    rw [intervalIntegral.smul_integral_comp_mul_add,
      intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  have htotal : L • (∫ x : ℝ, f (L * x + τ)) = ∫ x, f x := by
    change L • (∫ x : ℝ, (fun y => f (y + τ)) (L * x)) = ∫ x, f x
    rw [Measure.integral_comp_mul_left (fun y : ℝ => f (y + τ)) L, integral_add_right_eq_self,
      abs_of_pos (inv_pos.mpr hL), smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  simpa only [zero_add, hi, htotal] using hs

/-- Integrating the nonnegative periodization over a frequency cell gives
exactly the full mass, uniformly in the location and length of the cell. -/
theorem lintegral_periodization {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) {L : ℝ} (hL : 0 < L) (τ : ℝ) :
    (∫⁻ u in Ioc τ (τ + L), ∑' n : ℤ, ENNReal.ofReal (f (u + L * n))) =
      ENNReal.ofReal (∫ u, f u) := by
  have hs := hasSum_integral_period_shifts hf hL τ
  have hle : τ ≤ τ + L := by linarith
  have hsum : Summable (fun n : ℤ => ∫ u in Ioc τ (τ + L), f (u + L * n)) := by
    simpa only [intervalIntegral.integral_of_le hle] using hs.summable
  have htotal : (∑' n : ℤ, ∫ u in Ioc τ (τ + L), f (u + L * n)) = ∫ u, f u := by
    simpa only [intervalIntegral.integral_of_le hle] using hs.tsum_eq
  rw [lintegral_tsum]
  · simp_rw [← ofReal_integral_eq_lintegral_ofReal
      (((hf.comp_add_right _).integrableOn)) (ae_of_all _ (fun u => hf0 _))]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun u => hf0 _)) hsum,
      htotal]
  · intro n
    exact (((hf.comp_add_right (L * n)).aestronglyMeasurable.restrict).aemeasurable).ennreal_ofReal

end WaveTurbulence.LemLin
