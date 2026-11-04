/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialOperatorBound
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Finite source spatial norms of actual smooth compact root cutoffs -/

public section
noncomputable section
open MeasureTheory
open scoped SchwartzMap ContDiff

namespace WaveTurbulence.Incoh

/-- Explicit source spatial coefficient of a Schwartz function. -/
@[expose] def schwartzSpatialConstant {d : ℕ} (N M : ℕ) (f : 𝓢(Mom d, ℂ)) : ℝ :=
  (2 : ℝ) ^ (M - 1) * ∑ j ∈ Finset.range (N + 1),
    ((SchwartzMap.seminorm ℝ 0 j) f + (SchwartzMap.seminorm ℝ M j) f)

/-- Actual Schwartz seminorms control the literal finite source spatial norm. -/
theorem spatialNorm_schwartz_le {d : ℕ} (N M : ℕ) (f : 𝓢(Mom d, ℂ)) :
    Fourier.spatialNorm N M f ≤ ENNReal.ofReal (schwartzSpatialConstant N M f) := by
  apply spatialNorm_le_of_weighted_operator_bound ((f.smooth ⊤).of_le (by simp))
  intro j hj k
  have hb : Fourier.momentumBracket k ≤ 1 + ‖k‖ := by
    unfold Fourier.momentumBracket
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [norm_nonneg k]
  have h0 := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f j k
  have hM := SchwartzMap.le_seminorm ℝ M j f k
  have hsum : ((SchwartzMap.seminorm ℝ 0 j) f + (SchwartzMap.seminorm ℝ M j) f) ≤
      ∑ i ∈ Finset.range (N + 1), ((SchwartzMap.seminorm ℝ 0 i) f + (SchwartzMap.seminorm ℝ M i) f) :=
    Finset.single_le_sum (fun i _ => add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (Finset.mem_range.mpr (by omega))
  calc
    _ ≤ (1 + ‖k‖) ^ M * ‖iteratedFDeriv ℝ j f k‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans (one_le_momentumBracket k)) hb M) (norm_nonneg _)
    _ ≤ (2 : ℝ) ^ (M - 1) * ((1 + ‖k‖ ^ M) * ‖iteratedFDeriv ℝ j f k‖) := by
      simpa only [one_pow, mul_assoc] using mul_le_mul_of_nonneg_right
        (add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg k) M) (norm_nonneg (iteratedFDeriv ℝ j f k))
    _ ≤ (2 : ℝ) ^ (M - 1) * ((SchwartzMap.seminorm ℝ 0 j) f + (SchwartzMap.seminorm ℝ M j) f) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [h0, hM]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Every actual smooth compact function has a finite source spatial norm at every finite order. -/
theorem exists_spatialNorm_bound_of_smooth_compact {d : ℕ} (N M : ℕ) {f : Mom d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ B : ℝ, 0 < B ∧ Fourier.spatialNorm N M f ≤ ENNReal.ofReal B := by
  let F := hc.toSchwartzMap hf
  let B := 1 + max 0 (schwartzSpatialConstant N M F)
  refine ⟨B, by dsimp only [B]; positivity, ?_⟩
  exact (spatialNorm_schwartz_le N M F).trans (ENNReal.ofReal_le_ofReal (by
    dsimp only [B]
    linarith only [le_max_right 0 (schwartzSpatialConstant N M F)]))

end WaveTurbulence.Incoh
