/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AngularMassEstimate
public import WaveTurbulence.Foundations.WKEL2.LossTwoPolar

/-!
# Uniform nonnegative estimate for the second loss kernel
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Proposition 5, with the resonant measure normalized without the delta factor one half. -/
theorem exists_uniform_lossTwo_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ f g : Mom d → ℝ,
      Measurable f → Measurable g → MemLp (weightedFunction s f) 2 →
      MemLp (weightedFunction s g) 2 → ∀ k : Mom d,
        (∫⁻ p, ENNReal.ofReal |f (k + p.1)| * ENNReal.ofReal |g (k + p.2)|
          ∂resonantMeasure e) ≤
          ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f * weightedL2Norm s g) := by
  obtain ⟨C, hC, hb⟩ := exists_angular_mass_bound hd s hs
  refine ⟨C, hC, fun e he f g hf hg hLf hLg k => ?_⟩
  rw [lintegral_lossTwo_polar he (by omega) hf hg k]
  exact hb e he f g hf hg hLf hLg k

end WaveTurbulence.WKEL2
