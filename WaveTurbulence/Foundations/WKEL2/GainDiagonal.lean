/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.LossOneBound
public import WaveTurbulence.Foundations.WKEL2.UnweightedL2
public import WaveTurbulence.Foundations.WKEL2.GainShift

/-!
# The diagonal integral in the gain Schur test

Research-note Proposition 7a: the first diagonal is controlled by Q₁.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The diagonal gain integral is bounded uniformly by the first-loss estimate. -/
theorem exists_gain_diagonal_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ F f g : Mom d → ℝ,
      Measurable F → Measurable f → Measurable g → MemLp F 2 →
      MemLp (weightedFunction s f) 2 → MemLp (weightedFunction s g) 2 →
      (∫⁻ q : Mom d × (Mom d × Mom d), ENNReal.ofReal ((F q.1) ^ 2) *
        ENNReal.ofReal |f (q.1 + q.2.1 + q.2.2)| * ENNReal.ofReal |g (q.1 + q.2.2)|
        ∂volume.prod (resonantMeasure e)) ≤
        (ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f * weightedL2Norm s g)) *
          ENNReal.ofReal ((weightedL2Norm 0 F) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_lossOne_bound hd s hs
  refine ⟨C, hC, fun e he F f g hF hf hg hLF hLf hLg => ?_⟩
  let := resonantMeasure_finiteOnCompacts e (by omega : 2 ≤ d)
  have hJ : Measurable (fun q : Mom d × (Mom d × Mom d) => ENNReal.ofReal ((F q.1) ^ 2) *
      ENNReal.ofReal |f (q.1 + q.2.1 + q.2.2)| * ENNReal.ofReal |g (q.1 + q.2.2)|) :=
    (((hF.pow_const 2).ennreal_ofReal.comp measurable_fst).mul
      (hf.abs.ennreal_ofReal.comp (by fun_prop))).mul (hg.abs.ennreal_ofReal.comp (by fun_prop))
  have hFsq : Measurable (fun k : Mom d => ENNReal.ofReal ((F k) ^ 2)) :=
    (hF.pow_const 2).ennreal_ofReal
  rw [lintegral_prod _ hJ.aemeasurable]
  calc
    _ ≤ ∫⁻ k : Mom d, ENNReal.ofReal ((F k) ^ 2) *
        (ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f * weightedL2Norm s g)) := by
      apply lintegral_mono
      intro k
      have hK : Measurable (fun p : Mom d × Mom d =>
          ENNReal.ofReal |f (k + p.1 + p.2)| * ENNReal.ofReal |g (k + p.2)|) :=
        (hf.abs.ennreal_ofReal.comp (by fun_prop)).mul (hg.abs.ennreal_ofReal.comp (by fun_prop))
      have heq := lintegral_const_mul (μ := resonantMeasure e) (ENNReal.ofReal ((F k) ^ 2)) hK
      have hb' := mul_le_mul' (le_refl (ENNReal.ofReal ((F k) ^ 2))) (hb e he f g hf hg hLf hLg k)
      calc
        _ = ENNReal.ofReal ((F k) ^ 2) * (∫⁻ p : Mom d × Mom d,
            ENNReal.ofReal |f (k + p.1 + p.2)| * ENNReal.ofReal |g (k + p.2)|
              ∂resonantMeasure e) := by simpa only [mul_assoc] using heq
        _ ≤ _ := hb'
    _ = _ := by
      rw [lintegral_mul_const _ hFsq, lintegral_sq_eq_ofReal_weightedL2Norm_zero hLF, mul_comm]

end WaveTurbulence.WKEL2
