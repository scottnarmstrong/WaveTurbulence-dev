/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # A common frequency envelope for the main-coefficient derivatives

DH23 (maincoef2) is integrated in frequency, whereas Prop6.4 is applied
at fixed frequency. The factorial gap (2k)!/(4k)! permits one integrable
envelope controlling EVERY derivative order, without any order-dependent
loss. Thus even the all-orders WordDerivL1 interface can be used.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped ENNReal

/-- The factorial gap dominates the exponential-series denominator. -/
theorem gevrey_ratio_le (A : ℝ) (hA : 0 ≤ A) (k : ℕ) :
    A ^ k * ((2 * k).factorial : ℝ) / (4 * k).factorial ≤ A ^ k / k.factorial := by
  have hnat : (2*k).factorial * k.factorial ≤ (4*k).factorial :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add (2*k) k)).trans
      (Nat.factorial_le (by omega))
  have hcast : ((2*k).factorial : ℝ) * k.factorial ≤ (4*k).factorial := by exact_mod_cast hnat
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc A ^ k * ((2*k).factorial : ℝ) * k.factorial = A ^ k * (((2*k).factorial : ℝ) * k.factorial) := by ring
    _ ≤ A ^ k * (4*k).factorial := mul_le_mul_of_nonneg_left hcast (pow_nonneg hA k)

theorem summable_gevrey_ratio (A : ℝ) (hA : 0 ≤ A) :
    Summable (fun k : ℕ => A ^ k * ((2*k).factorial : ℝ) / (4*k).factorial) :=
  Summable.of_nonneg_of_le (fun _ => by positivity) (gevrey_ratio_le A hA)
    (Real.summable_pow_div_factorial A)

/-- One envelope simultaneously controls countably many integrated
Gevrey derivative norms. All dependence on A is in a finite scalar series. -/
theorem lintegral_gevrey_envelope_le {Λ : Type*} [MeasurableSpace Λ] {μ : Measure Λ}
    (G : ℕ → Λ → ℝ≥0∞) (hGm : ∀ k, Measurable (G k)) {N A : ℝ}
    (hN : 0 ≤ N)
    (hG : ∀ k, ∫⁻ ω, G k ω ∂μ ≤ ENNReal.ofReal (N * A ^ k * (2*k).factorial)) :
    ∫⁻ ω, (∑' k : ℕ, ENNReal.ofReal (1 / ((4*k).factorial : ℝ)) * G k ω) ∂μ ≤
      ENNReal.ofReal N * ∑' k : ℕ, ENNReal.ofReal (A ^ k * ((2*k).factorial : ℝ) / (4*k).factorial) := by
  rw [lintegral_tsum (fun k => ((hGm k).const_mul _).aemeasurable),← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  rw [lintegral_const_mul _ (hGm k)]
  calc ENNReal.ofReal (1 / ((4*k).factorial : ℝ)) * (∫⁻ ω, G k ω ∂μ)
      ≤ ENNReal.ofReal (1 / ((4*k).factorial : ℝ)) * ENNReal.ofReal (N * A ^ k * (2*k).factorial) :=
        mul_le_mul_right (hG k) _
    _ = ENNReal.ofReal N * ENNReal.ofReal (A ^ k * ((2*k).factorial : ℝ) / (4*k).factorial) := by
      rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul hN]
      congr 1
      ring

/-- The common derivative envelope is finite in integral, hence finite ae. -/
theorem lintegral_gevrey_envelope_lt_top {Λ : Type*} [MeasurableSpace Λ] {μ : Measure Λ}
    (G : ℕ → Λ → ℝ≥0∞) (hGm : ∀ k, Measurable (G k)) {N A : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hG : ∀ k, ∫⁻ ω, G k ω ∂μ ≤ ENNReal.ofReal (N * A ^ k * (2*k).factorial)) :
    ∫⁻ ω, (∑' k : ℕ, ENNReal.ofReal (1 / ((4*k).factorial : ℝ)) * G k ω) ∂μ < ⊤ := by
  exact (lintegral_gevrey_envelope_le G hGm hN hG).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (summable_gevrey_ratio A hA).tsum_ofReal_lt_top)

end WaveTurbulence.RegAsymp
