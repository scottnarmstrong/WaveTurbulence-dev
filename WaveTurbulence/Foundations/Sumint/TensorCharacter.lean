/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.FiniteWeightExpansion

/-!
# Tensor Fourier characters preserve absolute coefficient mass

The spatial momentum argument is fixed here. The Fourier frequencies
range independently over a finite product of Euclidean spaces.
-/

public section

open MeasureTheory Finset

namespace WaveTurbulence.Sumint

/-- The simultaneous modulation for a finite family of momentum arguments. -/
@[expose] noncomputable def tensorCharacter {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → Mom d) (ξ : ι → Mom d) : ℂ :=
  ∏ i, (Real.fourierChar (inner ℝ (ξ i) (p i)) : ℂ)

/-- Tensor characters have unit modulus. -/
theorem norm_tensorCharacter {ι : Type*} [Fintype ι] {d : ℕ}
    (p ξ : ι → Mom d) : ‖tensorCharacter p ξ‖ = 1 := by
  simp only [tensorCharacter, norm_prod, Circle.norm_coe, prod_const_one]

/-- The modulation is continuous in its frequency vector. -/
theorem continuous_tensorCharacter {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → Mom d) : Continuous (tensorCharacter p) := by
  unfold tensorCharacter
  simp_rw [Real.fourierChar_apply]
  fun_prop

/-- No coefficient mass is lost under the tensor character. -/
theorem integral_norm_tensorCharacter_mul {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → Mom d) (F : (ι → Mom d) → ℂ) :
    (∫ ξ, ‖tensorCharacter p ξ*F ξ‖) = ∫ ξ, ‖F ξ‖ := by
  simp only [norm_mul, norm_tensorCharacter, one_mul]

end WaveTurbulence.Sumint
