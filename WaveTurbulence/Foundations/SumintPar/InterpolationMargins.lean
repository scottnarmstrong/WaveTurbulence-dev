/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.Data
import Mathlib.Tactic

/-!
# Explicit interpolation parameters and exponent margins for sumint

The interpolation weight between `-η^8` and `1/4` is
`12η^8/(1+4η^8)`. The partition scale is `β=η^7 sqrt η`.
These formulas account for the source's `14d` loss and both sets of
three cutoff and three partition losses.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- The precise interpolation weight giving the target regularity. -/
@[expose] noncomputable def interpolationWeight (η : ℝ) : ℝ :=
  12 * η^8 / (1 + 4 * η^8)

/-- The source partition exponent `η^(15/2)`, with its positive square root explicit. -/
@[expose] noncomputable def partitionExponent (η : ℝ) : ℝ := η^7 * Real.sqrt η

/-- Interpolating the negative and positive regularities gives exactly `2η^8`. -/
theorem interpolation_regularity (η : ℝ) :
    (1 - interpolationWeight η) * (-η^8) + interpolationWeight η * (1/4) = 2 * η^8 := by
  have hp : 0 < 1 + 4 * η^8 := by positivity
  unfold interpolationWeight
  field_simp
  <;> ring

/-- The positive endpoint is used with weight at most `12η^8`. -/
theorem interpolationWeight_bounds {η : ℝ} (hη : 0 ≤ η) (hsmall : 8 * η^8 ≤ 1) :
    0 ≤ interpolationWeight η ∧ interpolationWeight η ≤ 1 ∧
      interpolationWeight η ≤ 12 * η^8 := by
  have hp : 0 < 1 + 4 * η^8 := by positivity
  unfold interpolationWeight
  refine ⟨by positivity, (div_le_iff₀ hp).mpr (by linarith), ?_⟩
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (η^8)]

/-- Reserve half of the final allowance for global cutoff constants depending on
`δ` and `Dsteps`; these constants must be absorbed by `L₀`, since `C₁` is chosen first. -/
theorem partition_interpolation_loss_le_half {d : ℕ} {η : ℝ}
    (hη : 0 ≤ η) (hsmall : 8 * η^8 ≤ 1)
    (hmargin : 12 * Real.sqrt η + 168 * (d : ℝ) * η ≤ 1/2) :
    12 * partitionExponent η + 14 * (d : ℝ) * interpolationWeight η ≤ η^7/2 := by
  have hw := (interpolationWeight_bounds hη hsmall).2.2
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right hmargin (pow_nonneg hη 7)
  have ht := mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num : (0 : ℝ) ≤ 14) hd)
  unfold partitionExponent
  nlinarith only [hm, ht]

end WaveTurbulence.SumintPar
