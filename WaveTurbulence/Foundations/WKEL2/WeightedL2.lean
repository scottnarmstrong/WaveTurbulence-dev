/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.WeightedL2Norm
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The frozen weighted norm and genuine L² membership

The multiplier is exactly the one in `weightedL2Norm`. Every use of the
Banach-space norm below includes actual `MemLp` membership.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The exact multiplier from the frozen weighted L² norm. -/
@[expose] def weightedFunction (s : ℝ) (f : Mom d → ℝ) (k : Mom d) : ℝ :=
  (1 + ‖k‖ ^ 2) ^ (s / 2) * f k

theorem weightedL2Norm_nonneg (s : ℝ) (f : Mom d → ℝ) : 0 ≤ weightedL2Norm s f :=
  Real.sqrt_nonneg _

/-- Squaring the frozen norm recovers its nonnegative squared integral. -/
theorem weightedL2Norm_sq (s : ℝ) (f : Mom d → ℝ) :
    (weightedL2Norm s f) ^ 2 = ∫ k, (weightedFunction s f k) ^ 2 :=
  Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

/-- Nonnegative lower-integral expression for the frozen norm squared. -/
theorem ofReal_weightedL2Norm_sq (s : ℝ) (f : Mom d → ℝ)
    (hf : MemLp (weightedFunction s f) 2) :
    ENNReal.ofReal ((weightedL2Norm s f) ^ 2) =
      ∫⁻ k, ENNReal.ofReal ((weightedFunction s f k) ^ 2) := by
  rw [weightedL2Norm_sq]
  exact ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- Measurability of the weighted input from Borel measurability of the input. -/
theorem measurable_weightedFunction (s : ℝ) {f : Mom d → ℝ} (hf : Measurable f) :
    Measurable (weightedFunction s f) := by
  have hb : Continuous (fun k : Mom d => 1 + ‖k‖ ^ 2) := by fun_prop
  exact (hb.rpow_const (fun _ => Or.inl (by positivity))).measurable.mul hf

/-- Generic real L² norm identity, avoiding any project-specific change of norm. -/
theorem sqrt_integral_sq_eq_norm_toLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : MemLp f 2 μ) :
    Real.sqrt (∫ x, (f x) ^ 2 ∂μ) = ‖hf.toLp f‖ := by
  have hsq : ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
    calc
      _ = ⟪hf.toLp f, hf.toLp f⟫_ℝ := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ x, ((hf.toLp f) x) ^ 2 ∂μ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only
          rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      _ = _ := integral_congr_ae (hf.coeFn_toLp.mono fun x hx => congrArg (fun r : ℝ => r ^ 2) hx)
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- The frozen norm equals the norm of its weighted L² representative. -/
theorem weightedL2Norm_eq_norm_toLp (s : ℝ) (f : Mom d → ℝ)
    (hf : MemLp (weightedFunction s f) 2) :
    weightedL2Norm s f = ‖hf.toLp (weightedFunction s f)‖ :=
  sqrt_integral_sq_eq_norm_toLp volume (weightedFunction s f) hf

end WaveTurbulence.WKEL2
