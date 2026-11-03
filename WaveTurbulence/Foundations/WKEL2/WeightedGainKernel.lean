/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantSupport
public import WaveTurbulence.Foundations.WKEL2.WeightedL2

/-!
# Nonnegative weight transfer for the gain kernel
-/

public section

noncomputable section

open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The output weight transfers to the first or third gain input on resonance. -/
theorem weighted_gain_kernel_le (s : ℝ) (hs : 0 ≤ s) (f₁ f₂ f₃ : Mom d → ℝ)
    (k a b : Mom d) (hab : ⟪a, b⟫_ℝ = 0) :
    ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) * ENNReal.ofReal |f₁ (k + a)| *
      ENNReal.ofReal |f₂ (k + a + b)| * ENNReal.ofReal |f₃ (k + b)| ≤
    ENNReal.ofReal ((2 : ℝ) ^ (s / 2)) *
      (ENNReal.ofReal |weightedFunction s f₁ (k + a)| * ENNReal.ofReal |f₂ (k + a + b)| *
          ENNReal.ofReal |f₃ (k + b)| +
        ENNReal.ofReal |f₁ (k + a)| * ENNReal.ofReal |f₂ (k + a + b)| *
          ENNReal.ofReal |weightedFunction s f₃ (k + b)|) := by
  have hw₁ : 0 ≤ (1 + ‖k + a‖ ^ 2) ^ (s / 2) := Real.rpow_nonneg (by positivity) _
  have hw₃ : 0 ≤ (1 + ‖k + b‖ ^ 2) ^ (s / 2) := Real.rpow_nonneg (by positivity) _
  have hc : 0 ≤ (2 : ℝ) ^ (s / 2) := Real.rpow_nonneg (by norm_num) _
  have hwt := ENNReal.ofReal_le_ofReal (weight_transfer s hs k a b hab)
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_add hw₁ hw₃] at hwt
  have h₁ : ENNReal.ofReal |weightedFunction s f₁ (k + a)| =
      ENNReal.ofReal ((1 + ‖k + a‖ ^ 2) ^ (s / 2)) * ENNReal.ofReal |f₁ (k + a)| := by
    rw [weightedFunction, abs_mul, abs_of_nonneg hw₁, ENNReal.ofReal_mul hw₁]
  have h₃ : ENNReal.ofReal |weightedFunction s f₃ (k + b)| =
      ENNReal.ofReal ((1 + ‖k + b‖ ^ 2) ^ (s / 2)) * ENNReal.ofReal |f₃ (k + b)| := by
    rw [weightedFunction, abs_mul, abs_of_nonneg hw₃, ENNReal.ofReal_mul hw₃]
  rw [h₁, h₃]
  calc
    _ = ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) *
        (ENNReal.ofReal |f₁ (k + a)| * ENNReal.ofReal |f₂ (k + a + b)| *
          ENNReal.ofReal |f₃ (k + b)|) := by ring
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ (s / 2)) *
        (ENNReal.ofReal ((1 + ‖k + a‖ ^ 2) ^ (s / 2)) +
          ENNReal.ofReal ((1 + ‖k + b‖ ^ 2) ^ (s / 2)))) *
        (ENNReal.ofReal |f₁ (k + a)| * ENNReal.ofReal |f₂ (k + a + b)| *
          ENNReal.ofReal |f₃ (k + b)|) := mul_le_mul' hwt le_rfl
    _ = _ := by ring

end WaveTurbulence.WKEL2
