/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantLocalFinite
public import WaveTurbulence.Foundations.WKEL2.Symmetry

/-!
# Compactly supported kernels satisfy the delta-reading hypotheses

This supplies the test functions needed for uniqueness of resonant measure.
-/

public section

open MeasureTheory Set Metric

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Every continuous compactly supported kernel satisfies the decay assumptions
used in the mollifier proof, for any exponent greater than the dimension. -/
theorem exists_deltaKernel_of_compactSupport (hd : 2 ≤ d)
    (F : Mom d → Mom d → ℝ) (hF : Continuous (Function.uncurry F))
    (hc : HasCompactSupport (Function.uncurry F)) (M : ℝ) (hM : (d : ℝ) < M) :
    ∃ A : Mom d → ℝ, DeltaKernel F A (fun _ => 0) M := by
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hc
  obtain ⟨R, hRpos, hR⟩ := hc.isBounded.exists_pos_norm_lt
  have hCpos : 0 ≤ C := (norm_nonneg (F 0 0)).trans (hC (0, 0))
  let D := C * (1 + R) ^ M
  let A : Mom d → ℝ := (ball 0 R).indicator (fun _ => D)
  have hD : 0 ≤ D := mul_nonneg hCpos (Real.rpow_nonneg (by linarith) _)
  refine ⟨A, hF, ?_, hM, ?_⟩
  · intro a x
    by_cases hz : F a x = 0
    · rw [hz, abs_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ => hD) a) (by positivity)
    · have hpair : ‖(a, x)‖ < R := hR (a, x) (subset_tsupport _ hz)
      have ha : a ∈ ball 0 R := mem_ball_zero_iff.mpr ((norm_fst_le _).trans_lt hpair)
      have hx : ‖x‖ < R := (norm_snd_le _).trans_lt hpair
      have hxp : 0 < 1 + ‖x‖ := by positivity
      have hpow : (1 + ‖x‖) ^ M ≤ (1 + R) ^ M :=
        Real.rpow_le_rpow (by positivity) (by linarith only [hx])
          (le_trans (Nat.cast_nonneg d) hM.le)
      have hbound : |F a x| ≤ C := by
        simpa only [Function.uncurry_apply_pair, Real.norm_eq_abs] using (hC (a, x))
      have hb : |F a x| * (1 + ‖x‖) ^ M ≤ D :=
        (mul_le_mul_of_nonneg_right hbound (by positivity)).trans
          (mul_le_mul_of_nonneg_left hpow hCpos)
      dsimp only [A]
      rw [indicator_of_mem ha, zero_add, Real.rpow_neg hxp.le]
      exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hxp M)).mpr hb
  · have hi := ((locallyIntegrable_inv_norm hd).integrableOn_isCompact
        (isCompact_closedBall (0 : Mom d) R)).mono_set ball_subset_closedBall
    have hh := hi.integrable_indicator measurableSet_ball
    have hh' := hh.mul_const D
    apply hh'.congr
    exact Filter.Eventually.of_forall fun a => by
      by_cases ha : a ∈ ball (0 : Mom d) R
      · simp only [A, indicator_of_mem ha]
      · simp only [A, indicator_of_notMem ha, zero_mul, mul_zero]

end WaveTurbulence.WKEL2
