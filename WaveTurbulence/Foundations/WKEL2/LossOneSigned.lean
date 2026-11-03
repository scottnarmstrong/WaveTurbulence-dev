/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.LossOneBound
public import WaveTurbulence.Foundations.WKEL2.ResonantIntegral

/-!
# The signed first loss operator
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Proposition 6 for signed Borel inputs, including genuine absolute integrability. -/
theorem exists_uniform_lossOne_signed (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ f g : Mom d → ℝ,
      Measurable f → Measurable g → MemLp (weightedFunction s f) 2 →
      MemLp (weightedFunction s g) 2 → ∀ k : Mom d,
        Integrable (fun p => f (k + p.1 + p.2) * g (k + p.2)) (resonantMeasure e) ∧
        |deltaInt (fun a b => f (k + a + b) * g (k + b))| ≤
          C * weightedL2Norm s f * weightedL2Norm s g := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_lossOne_bound hd s hs
  refine ⟨C / 2, by positivity, fun e he f g hf hg hLf hLg k => ?_⟩
  let F : Mom d × Mom d → ℝ := fun p => f (k + p.1 + p.2) * g (k + p.2)
  have hm : Measurable F :=
    (hf.comp (by fun_prop)).mul
      (hg.comp (continuous_const.add continuous_snd).measurable)
  have hnorm : (∫⁻ p, ENNReal.ofReal ‖F p‖ ∂resonantMeasure e) ≤
      ENNReal.ofReal (C * (weightedL2Norm s f * weightedL2Norm s g)) := by
    simpa only [F, norm_mul, Real.norm_eq_abs, ENNReal.ofReal_mul (abs_nonneg _),
      ENNReal.ofReal_mul hC] using hb e he f g hf hg hLf hLg k
  have hi : Integrable F (resonantMeasure e) :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_norm F).mpr
      (hnorm.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  have hreal := (norm_integral_le_lintegral_norm (μ := resonantMeasure e) F).trans
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm)
  rw [ENNReal.toReal_ofReal (mul_nonneg hC
      (mul_nonneg (weightedL2Norm_nonneg _ _) (weightedL2Norm_nonneg _ _))),
    integral_resonantMeasure_eq_two_deltaInt he hi, norm_mul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hreal
  change |deltaInt (fun a b => f (k + a + b) * g (k + b))| ≤ _
  dsimp only [F] at hreal
  rw [Real.norm_eq_abs] at hreal
  nlinarith only [hreal]

end WaveTurbulence.WKEL2
