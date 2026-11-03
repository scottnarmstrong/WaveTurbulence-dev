/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Moment tails and countable union bounds

The Chebyshev/Markov estimates used in TARGET's exceptional-event arguments.
Moment integrability is the source analytic premise. Countable unions are
stated with extended nonnegative bounds so no summability premise is needed.
-/

public section

namespace WaveTurbulence.Probability
open MeasureTheory
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω}

/-- Markov's inequality at any positive integer moment, using a real threshold. -/
theorem measureReal_norm_ge_le_moment [IsFiniteMeasure μ] {X : Ω → E} {n : ℕ}
    (hn : n ≠ 0) (hX : Integrable (fun ω => ‖X ω‖ ^ n) μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ‖X ω‖} ≤ (∫ ω, ‖X ω‖ ^ n ∂μ) / t ^ n := by
  have heq : {ω | t ^ n ≤ ‖X ω‖ ^ n} = {ω | t ≤ ‖X ω‖} := by
    ext ω
    exact pow_le_pow_iff_left₀ ht.le (norm_nonneg _) hn
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => pow_nonneg (norm_nonneg (X ω)) n) hX (t ^ n)
  rw [heq] at h
  exact (le_div_iff₀ (pow_pos ht n)).mpr (by simpa only [mul_comm] using h)

/-- The even `2P` moment form used for complex random variables in TARGET. -/
theorem measureReal_norm_ge_le_even_moment [IsFiniteMeasure μ] {X : Ω → E} {P : ℕ}
    (hP : 0 < P) (hX : Integrable (fun ω => ‖X ω‖ ^ (2 * P)) μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ‖X ω‖} ≤ (∫ ω, ‖X ω‖ ^ (2 * P) ∂μ) / t ^ (2 * P) :=
  measureReal_norm_ge_le_moment (by omega) hX ht

/-- Countable union bound with arbitrary extended nonnegative error budgets. -/
theorem measure_iUnion_le_tsum {ι : Type*} [Countable ι] (A : ι → Set Ω)
    (ε : ι → ℝ≥0∞) (hA : ∀ i, μ (A i) ≤ ε i) : μ (⋃ i, A i) ≤ ∑' i, ε i :=
  (MeasureTheory.measure_iUnion_le A).trans (ENNReal.tsum_le_tsum hA)

/-- A countable family of nonnegative moments controls the union of its tails. -/
theorem measure_iUnion_norm_ge_le_lintegral {ι : Type*} [Countable ι]
    (X : ι → Ω → E) (hX : ∀ i, AEMeasurable (fun ω => ‖X i ω‖ₑ) μ)
    (t : ι → ℝ≥0∞) (ht0 : ∀ i, t i ≠ 0) (htop : ∀ i, t i ≠ ⊤)
    {P : ℕ} :
    μ (⋃ i, {ω | t i ≤ ‖X i ω‖ₑ}) ≤
      ∑' i, (∫⁻ ω, ‖X i ω‖ₑ ^ (2 * P) ∂μ) / t i ^ (2 * P) := by
  apply measure_iUnion_le_tsum
  intro i
  have hsub : {ω | t i ≤ ‖X i ω‖ₑ} ⊆
      {ω | t i ^ (2 * P) ≤ ‖X i ω‖ₑ ^ (2 * P)} :=
    by
      intro ω h
      change t i ≤ ‖X i ω‖ₑ at h
      change t i ^ (2 * P) ≤ ‖X i ω‖ₑ ^ (2 * P)
      exact pow_le_pow_left' h _
  exact (measure_mono hsub).trans
    (meas_ge_le_lintegral_div ((hX i).pow_const _) (pow_ne_zero _ (ht0 i))
      (ENNReal.pow_ne_top (htop i)))

end WaveTurbulence.Probability
