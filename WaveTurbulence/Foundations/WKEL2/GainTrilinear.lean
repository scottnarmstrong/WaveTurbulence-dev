/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.GainSquareBound
public import WaveTurbulence.Foundations.WKEL2.SignedGainIntegral
public import WaveTurbulence.Foundations.WKEL2.L2Majorant

/-!
# The signed weighted L² gain estimate

Research-note Proposition 7 and the j = 0 case of Theorem 7. Absolute
integrability of the resonant kernel holds almost everywhere in the output
momentum and is proved before the intrinsic delta formula is used.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The signed gain estimate in the exact frozen weighted norm, with actual L² membership. -/
theorem exists_collisionTerm_zero_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f₁ f₂ f₃ : Mom d → ℝ,
      Measurable f₁ → Measurable f₂ → Measurable f₃ →
      MemLp (weightedFunction s f₁) 2 → MemLp (weightedFunction s f₂) 2 →
      MemLp (weightedFunction s f₃) 2 →
      MemLp (weightedFunction s (collisionTerm 0 f₁ f₂ f₃)) 2 ∧
      weightedL2Norm s (collisionTerm 0 f₁ f₂ f₃) ≤
        C * weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃ := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : Mom d)
  let e := unitVec v
  have he : ‖e‖ = 1 := norm_unitVec hv
  obtain ⟨C, hC, hb⟩ := exists_weighted_absoluteGain_square_bound hd s hs
  refine ⟨C / 2, by positivity, fun f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃ => ?_⟩
  let G : Mom d → ℝ≥0∞ := fun k =>
    ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) * absoluteGain e f₁ f₂ f₃ k
  let B := C * (weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃)
  have hB : 0 ≤ B := mul_nonneg hC
    (mul_nonneg (mul_nonneg (weightedL2Norm_nonneg _ _) (weightedL2Norm_nonneg _ _))
      (weightedL2Norm_nonneg _ _))
  have hG : Measurable G := (measurable_frozenWeight s).mul
    (measurable_absoluteGain e (by omega) h₁ h₂ h₃)
  have hSq : (∫⁻ k, (G k) ^ 2) ≤ ENNReal.ofReal (B ^ 2) := hb e he f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃
  have hGfin : ∀ᵐ k : Mom d, G k < ⊤ := by
    have h := ae_lt_top (hG.pow_const 2) (ne_of_lt (hSq.trans_lt ENNReal.ofReal_lt_top))
    filter_upwards [h] with k hk
    rcases ENNReal.pow_lt_top_iff.mp hk with hk | hz
    · exact hk
    · norm_num at hz
  have hAbsFin : ∀ᵐ k : Mom d, absoluteGain e f₁ f₂ f₃ k < ⊤ := by
    filter_upwards [hGfin] with k hk
    change ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) * absoluteGain e f₁ f₂ f₃ k < ⊤ at hk
    rcases ENNReal.mul_lt_top_iff.mp hk with hh | hz | hz
    · exact hh.2
    · have hpos : 0 < ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) :=
        ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) (s / 2))
      exact False.elim (hpos.ne' hz)
    · rw [hz]
      exact ENNReal.zero_lt_top
  have heq : ∀ᵐ k : Mom d, resonantGain e f₁ f₂ f₃ k = collisionTerm 0 f₁ f₂ f₃ k := by
    filter_upwards [hAbsFin] with k hk
    exact resonantGain_eq_collisionTerm_zero he f₁ f₂ f₃ k
      (integrable_gainKernel_of_absoluteGain_lt_top e h₁ h₂ h₃ k hk)
  have hweighted : weightedFunction s (resonantGain e f₁ f₂ f₃) =ᵐ[volume]
      weightedFunction s (collisionTerm 0 f₁ f₂ f₃) := by
    filter_upwards [heq] with k hk
    exact congrArg (fun r : ℝ => (1 + ‖k‖ ^ 2) ^ (s / 2) * r) hk
  have hmeas : AEStronglyMeasurable (weightedFunction s (collisionTerm 0 f₁ f₂ f₃)) volume :=
    (measurable_weightedFunction s (measurable_resonantGain e (by omega) h₁ h₂ h₃)).aestronglyMeasurable.congr hweighted
  have hmajorant : ∀ᵐ k : Mom d,
      ENNReal.ofReal |weightedFunction s (collisionTerm 0 f₁ f₂ f₃) k| ≤
        ENNReal.ofReal (1 / 2 : ℝ) * G k := by
    filter_upwards [hweighted] with k hk
    have hw : 0 ≤ (1 + ‖k‖ ^ 2) ^ (s / 2) := Real.rpow_nonneg (by positivity) _
    rw [← hk, weightedFunction, abs_mul, abs_of_nonneg hw, ENNReal.ofReal_mul hw]
    have h := mul_le_mul' (le_refl (ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2))))
      (ofReal_abs_resonantGain_le e f₁ f₂ f₃ k)
    exact h.trans_eq (by dsimp only [G]; ac_rfl)
  obtain ⟨hi, hn⟩ := memLp_and_norm_le_of_sq_majorant hmeas hmajorant (B / 2)
    (by positivity) (lintegral_half_sq_bound hG B hSq)
  rw [weightedL2Norm_zero_weightedFunction] at hn
  refine ⟨hi, hn.trans_eq ?_⟩
  dsimp only [B]
  ring

end WaveTurbulence.WKEL2
