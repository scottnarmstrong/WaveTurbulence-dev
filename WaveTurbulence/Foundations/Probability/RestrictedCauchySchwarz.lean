/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Cauchy–Schwarz for unnormalized restricted expectations

TARGET L813–L819: expectations under an event integrate against `μ.restrict A`.
No normalization by the event probability is introduced.
-/

public section

namespace WaveTurbulence.Probability
open MeasureTheory
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Restricted Cauchy–Schwarz supplies a square-root event-measure factor. -/
theorem norm_setIntegral_le_sqrt_measure_mul {f : Ω → E} (hf : MemLp f 2 μ)
    (A : Set Ω) :
    ‖∫ ω in A, f ω ∂μ‖ ≤ Real.sqrt (μ.real A) *
      Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) := by
  have hfA := (hf.restrict A).norm
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 (μ.restrict A) := memLp_const _
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun ω => norm_nonneg (f ω))
    (Filter.Eventually.of_forall fun _ => zero_le_one)
    (by simpa using hfA) (by simpa using h1)
  have hpow : (fun ω => ‖f ω‖ ^ (2 : ℝ)) = (fun ω => ‖f ω‖ ^ (2 : ℕ)) := by
    funext ω
    exact Real.rpow_natCast _ 2
  simp only [mul_one, Real.one_rpow, hpow, integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ, ← Real.sqrt_eq_rpow] at h
  have hint : Integrable (fun ω => ‖f ω‖ ^ 2) μ := hf.integrable_norm_pow (by decide)
  have hmono : (∫ ω in A, ‖f ω‖ ^ 2 ∂μ) ≤ ∫ ω, ‖f ω‖ ^ 2 ∂μ :=
    integral_mono_measure μ.restrict_le_self (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint
  calc
    _ ≤ ∫ ω in A, ‖f ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ Real.sqrt (∫ ω in A, ‖f ω‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) := h
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _)

end WaveTurbulence.Probability
