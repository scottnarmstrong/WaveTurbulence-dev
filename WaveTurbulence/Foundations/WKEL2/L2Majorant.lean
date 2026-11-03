/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.UnweightedL2
public import WaveTurbulence.Foundations.WKEL2.GainCauchyAlgebra

/-!
# Actual L² membership from an extended nonnegative squared majorant
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- An almost everywhere squared majorant gives genuine membership and the frozen zero-weight norm bound. -/
theorem memLp_and_norm_le_of_sq_majorant {f : Mom d → ℝ}
    (hf : AEStronglyMeasurable f volume) {G : Mom d → ℝ≥0∞}
    (hmajorant : ∀ᵐ k, ENNReal.ofReal |f k| ≤ G k) (B : ℝ) (hB : 0 ≤ B)
    (hSq : (∫⁻ k, (G k) ^ 2) ≤ ENNReal.ofReal (B ^ 2)) :
    MemLp f 2 ∧ weightedL2Norm 0 f ≤ B := by
  have hsq : (∫⁻ k, ENNReal.ofReal ((f k) ^ 2)) ≤ ENNReal.ofReal (B ^ 2) := by
    refine (lintegral_mono_ae (hmajorant.mono fun k hk => ?_)).trans hSq
    rw [← ennreal_ofReal_abs_sq]
    simpa only [pow_two] using mul_le_mul' hk hk
  have hm : AEStronglyMeasurable (fun k => (f k) ^ 2) volume := by
    refine (hf.mul hf).congr (Filter.Eventually.of_forall fun k => ?_)
    simp only [Pi.mul_apply, pow_two]
  have hi : Integrable (fun k => (f k) ^ 2) := by
    refine ⟨hm, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsq.trans_lt ENNReal.ofReal_lt_top
  have hLp := (memLp_two_iff_integrable_sq hf).mpr hi
  refine ⟨hLp, ?_⟩
  rw [lintegral_sq_eq_ofReal_weightedL2Norm_zero hLp] at hsq
  have hreal := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg B)).mp hsq
  exact (sq_le_sq₀ (weightedL2Norm_nonneg _ _) hB).mp hreal

/-- Scaling a squared extended integral by the delta factor one half. -/
theorem lintegral_half_sq_bound {G : Mom d → ℝ≥0∞} (hG : Measurable G)
    (B : ℝ) (hSq : (∫⁻ k, (G k) ^ 2) ≤ ENNReal.ofReal (B ^ 2)) :
    (∫⁻ k, (ENNReal.ofReal (1 / 2 : ℝ) * G k) ^ 2) ≤ ENNReal.ofReal ((B / 2) ^ 2) := by
  simp_rw [mul_pow]
  rw [lintegral_const_mul _ (hG.pow_const 2)]
  calc
    _ ≤ (ENNReal.ofReal (1 / 2 : ℝ)) ^ 2 * ENNReal.ofReal (B ^ 2) := mul_le_mul' le_rfl hSq
    _ = _ := by
      rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2) 2,
        ← ENNReal.ofReal_mul (sq_nonneg (1 / 2 : ℝ))]
      congr 1
      ring

end WaveTurbulence.WKEL2
