/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AllMoments
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
/-! Natural powers preserve availability of all positive finite moments. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory
open scoped ENNReal

theorem memLp_pow_of_all {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (M : Ω → ℝ) (hM : ∀ p : ℕ, 1 ≤ p → MemLp M (p : ℝ≥0∞) μ)
    (h0 : ∀ ω, 0 ≤ M ω) (k q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => M ω ^ k) (q : ℝ≥0∞) μ := by
  by_cases hk : k = 0
  · subst k
    simpa only [pow_zero] using memLp_const (1 : ℝ)
  have hk1 : 1 ≤ k := by omega
  have hqk : 1 ≤ q * k := by nlinarith
  have h := (hM (q * k) hqk).norm_rpow_div (k : ℝ≥0∞)
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk
  simpa only [Nat.cast_mul, ENNReal.mul_div_cancel_right hk0 (by finiteness),
    ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_of_nonneg (h0 _)] using h

end WaveTurbulence.Induct
