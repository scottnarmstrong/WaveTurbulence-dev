/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.GainTrilinear
public import WaveTurbulence.Foundations.WKEL2.LossOneSigned
public import WaveTurbulence.Foundations.WKEL2.LossTwoSigned
public import WaveTurbulence.Foundations.WKEL2.ResonantSignedSymmetry

/-!
# Actual resonant-kernel integrability for weighted L² inputs

This supports the full collision decomposition and its multilinearity on the
Banach weighted-L² model. No integrability hypothesis is added to the source
trilinear estimate.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Absolute gain is finite almost everywhere for genuine weighted L² inputs. -/
theorem ae_absoluteGain_lt_top (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s)
    {e : Mom d} (he : ‖e‖ = 1) {f₁ f₂ f₃ : Mom d → ℝ}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃)
    (hL₁ : MemLp (weightedFunction s f₁) 2) (hL₂ : MemLp (weightedFunction s f₂) 2)
    (hL₃ : MemLp (weightedFunction s f₃) 2) :
    ∀ᵐ k : Mom d, absoluteGain e f₁ f₂ f₃ k < ⊤ := by
  obtain ⟨C, hC, hb⟩ := exists_weighted_absoluteGain_square_bound hd s hs
  let G : Mom d → ℝ≥0∞ := fun k =>
    ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) * absoluteGain e f₁ f₂ f₃ k
  have hm : Measurable G := (measurable_frozenWeight s).mul
    (measurable_absoluteGain e (by omega) h₁ h₂ h₃)
  have hf := ae_lt_top (hm.pow_const 2)
    (ne_of_lt ((hb e he f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃).trans_lt ENNReal.ofReal_lt_top))
  filter_upwards [hf] with k hk
  have hk' : G k < ⊤ := by
    rcases ENNReal.pow_lt_top_iff.mp hk with hh | hz
    · exact hh
    · norm_num at hz
  change ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) * absoluteGain e f₁ f₂ f₃ k < ⊤ at hk'
  rcases ENNReal.mul_lt_top_iff.mp hk' with hh | hz | hz
  · exact hh.2
  · have hp : 0 < ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
    exact False.elim (hp.ne' hz)
  · rw [hz]
    exact ENNReal.zero_lt_top

/-- Every collision-term kernel is genuinely integrable for almost every output momentum. -/
theorem ae_integrable_collisionKernel (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s)
    {e : Mom d} (he : ‖e‖ = 1) {f₁ f₂ f₃ : Mom d → ℝ}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃)
    (hL₁ : MemLp (weightedFunction s f₁) 2) (hL₂ : MemLp (weightedFunction s f₂) 2)
    (hL₃ : MemLp (weightedFunction s f₃) 2) (j : Fin 4) :
    ∀ᵐ k : Mom d, Integrable (fun p : Mom d × Mom d =>
      collisionKernel j f₁ f₂ f₃ k p.1 p.2) (resonantMeasure e) := by
  fin_cases j
  · filter_upwards [ae_absoluteGain_lt_top hd s hs he h₁ h₂ h₃ hL₁ hL₂ hL₃] with k hk
    exact integrable_gainKernel_of_absoluteGain_lt_top e h₁ h₂ h₃ k hk
  · obtain ⟨C, hC, hb⟩ := exists_uniform_lossOne_signed hd s hs
    apply Filter.Eventually.of_forall
    intro k
    have hi := (hb e he f₂ f₃ h₂ h₃ hL₂ hL₃ k).1.const_mul (f₁ k)
    refine hi.congr (Filter.Eventually.of_forall fun p => ?_)
    dsimp only [collisionKernel]
    ring
  · obtain ⟨C, hC, hb⟩ := exists_uniform_lossTwo_signed hd s hs
    apply Filter.Eventually.of_forall
    intro k
    have hi := (hb e he f₁ f₃ h₁ h₃ hL₁ hL₃ k).1.const_mul (f₂ k)
    refine hi.congr (Filter.Eventually.of_forall fun p => ?_)
    dsimp only [collisionKernel]
    ring
  · obtain ⟨C, hC, hb⟩ := exists_uniform_lossOne_signed hd s hs
    apply Filter.Eventually.of_forall
    intro k
    have hi := (integrable_resonant_swap he (by omega)
      (hb e he f₂ f₁ h₂ h₁ hL₂ hL₁ k).1).const_mul (f₃ k)
    refine hi.congr (Filter.Eventually.of_forall fun p => ?_)
    dsimp only [collisionKernel]
    rw [show k + p.2 + p.1 = k + p.1 + p.2 by abel]
    ring

end WaveTurbulence.WKEL2
