/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CodimTwoSlice

/-!
# Nonnegative form of the uniform codimension-two decay bound
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The transverse constant in research-note Proposition 6. -/
@[expose] def transverseDecayMass (d : ℕ) (s : ℝ) : ℝ :=
  ∫ z : Mom (d - 1 - 1), japaneseDecay (2 * s) z

theorem transverseDecayMass_nonneg (d : ℕ) (s : ℝ) : 0 ≤ transverseDecayMass d s :=
  integral_nonneg fun z => japaneseDecay_nonneg _ z

/-- Uniform affine-slice bound, allowing Tonelli without a priori integrability. -/
theorem lintegral_codimTwoSlice_le (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {θ : Mom d} (hθ : θ ≠ 0)
    {η : Mom (d - 1)} (hη : η ≠ 0) (k : Mom d) (t u : ℝ) :
    (∫⁻ z, ENNReal.ofReal (japaneseDecay (2 * s) (k + codimTwoSlice hθ hη t u z))) ≤
      ENNReal.ofReal (transverseDecayMass d s) := by
  obtain ⟨hi, hb⟩ := integral_codimTwoSlice_le hd s hs hθ hη k t u
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => japaneseDecay_nonneg _ _)]
  exact ENNReal.ofReal_le_ofReal hb

end WaveTurbulence.WKEL2
