/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.L2DualTruncation

/-!
# Nonnegative L² membership from real L² tests

This lemma applies to extended outputs before finiteness is known. Bounded
finite-support truncations are genuine real L² tests, and monotone
convergence gives the squared-integral bound.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Squares of an increasing extended nonnegative sequence exhaust the square of its supremum. -/
theorem ennreal_sq_iSup_le_iSup_sq {f : ℕ → ℝ≥0∞} (hf : Monotone f) :
    (⨆ n, f n) ^ 2 ≤ ⨆ n, (f n) ^ 2 := by
  rw [pow_two, ENNReal.iSup_mul]
  apply iSup_le
  intro i
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro j
  apply le_iSup_of_le (max i j)
  simpa only [pow_two] using mul_le_mul' (hf (Nat.le_max_left i j)) (hf (Nat.le_max_right i j))

/-- A nonnegative extended function bounded against every real L² test has bounded squared integral. -/
theorem lintegral_sq_le_of_l2_tests {G : Mom d → ℝ≥0∞} (hG : Measurable G)
    (B : ℝ) (hB : 0 ≤ B)
    (htest : ∀ F : Mom d → ℝ, Measurable F → MemLp F 2 →
      (∫⁻ k, G k * ENNReal.ofReal |F k|) ≤
        ENNReal.ofReal B * ENNReal.ofReal (weightedL2Norm 0 F)) :
    (∫⁻ k, (G k) ^ 2) ≤ ENNReal.ofReal (B ^ 2) := by
  have hbound (n : ℕ) : (∫⁻ k, (dualTruncationNN G n k) ^ 2) ≤ ENNReal.ofReal (B ^ 2) := by
    let T := dualTruncation G n
    have hm : Measurable T := measurable_dualTruncation hG n
    have hLp : MemLp T 2 := memLp_dualTruncation hG n
    have hnon (k : Mom d) : 0 ≤ T k := dualTruncation_nonneg G n k
    have hpoint (k : Mom d) : ENNReal.ofReal ((T k) ^ 2) ≤ G k * ENNReal.ofReal |T k| := by
      rw [abs_of_nonneg (hnon k), ENNReal.ofReal_pow (hnon k) 2]
      change (ENNReal.ofReal (dualTruncation G n k)) ^ 2 ≤
        G k * ENNReal.ofReal (dualTruncation G n k)
      rw [ofReal_dualTruncation, pow_two]
      exact mul_le_mul' (dualTruncationNN_le G n k) le_rfl
    have htestn := (lintegral_mono hpoint).trans (htest T hm hLp)
    rw [lintegral_sq_eq_ofReal_weightedL2Norm_zero hLp, ← ENNReal.ofReal_mul hB] at htestn
    have hN : 0 ≤ weightedL2Norm 0 T := weightedL2Norm_nonneg _ _
    have hreal : (weightedL2Norm 0 T) ^ 2 ≤ B * weightedL2Norm 0 T :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hN)).mp htestn
    have hnorm : weightedL2Norm 0 T ≤ B := by
      by_cases hz : weightedL2Norm 0 T = 0
      · simpa only [hz] using hB
      · have hp : 0 < weightedL2Norm 0 T := lt_of_le_of_ne hN (Ne.symm hz)
        rw [pow_two] at hreal
        exact le_of_mul_le_mul_right hreal hp
    calc
      _ = ∫⁻ k, ENNReal.ofReal ((T k) ^ 2) := by
        apply lintegral_congr
        intro k
        rw [ENNReal.ofReal_pow (hnon k) 2]
        exact congrArg (fun z : ℝ≥0∞ => z ^ 2) (ofReal_dualTruncation G n k).symm
      _ = ENNReal.ofReal ((weightedL2Norm 0 T) ^ 2) :=
        lintegral_sq_eq_ofReal_weightedL2Norm_zero hLp
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((sq_le_sq₀ hN hB).mpr hnorm)
  have hmono : Monotone (fun n => fun k : Mom d => (dualTruncationNN G n k) ^ 2) := by
    intro i j hij k
    have h := dualTruncationNN_mono G hij k
    simpa only [pow_two] using mul_le_mul' h h
  have hpoint (k : Mom d) : (G k) ^ 2 ≤ ⨆ n, (dualTruncationNN G n k) ^ 2 := by
    calc
      _ = (⨆ n, dualTruncationNN G n k) ^ 2 := by rw [iSup_dualTruncationNN]
      _ ≤ _ := ennreal_sq_iSup_le_iSup_sq (fun i j hij => dualTruncationNN_mono G hij k)
  calc
    _ ≤ ∫⁻ k, ⨆ n, (dualTruncationNN G n k) ^ 2 := lintegral_mono hpoint
    _ = ⨆ n, ∫⁻ k, (dualTruncationNN G n k) ^ 2 :=
      lintegral_iSup (fun n => (measurable_dualTruncationNN hG n).pow_const 2) hmono
    _ ≤ _ := iSup_le hbound

end WaveTurbulence.WKEL2
