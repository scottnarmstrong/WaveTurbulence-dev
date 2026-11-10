/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentAssembly
public import WaveTurbulence.Foundations.CountLemmas.PowerAbsorption
/-! Small-delta and large-L absorption in the assembled incoherent contribution. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter

theorem prefactor_pow_le {A b c : ℝ} (hA : 1 ≤ A) (hb : 0 ≤ b) (hab : A * b ≤ c)
    {n : ℕ} (hn : 1 ≤ n) : A * b ^ n ≤ c ^ n := by
  calc
    A * b ^ n ≤ A ^ n * b ^ n := mul_le_mul_of_nonneg_right
      (le_self_pow₀ hA (by omega)) (pow_nonneg hb _)
    _ = (A * b) ^ n := (mul_pow _ _ _).symm
    _ ≤ c ^ n := pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hA) hb) hab _

/-- An explicit positive threshold gives the small-delta condition, independent of order n. -/
theorem scaled_delta_le_sqrt {A δ : ℝ} (hA : 0 < A) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ (A⁻¹) ^ 2) : A * δ ≤ Real.sqrt δ := by
  have hs : Real.sqrt δ ≤ A⁻¹ := (Real.sqrt_le_iff).mpr ⟨inv_nonneg.mpr hA.le, hsmall⟩
  have hmul : A * Real.sqrt δ ≤ 1 := by
    simpa only [mul_inv_cancel₀ hA.ne'] using mul_le_mul_of_nonneg_left hs hA.le
  calc
    A * δ = (A * Real.sqrt δ) * Real.sqrt δ := by rw [mul_assoc, Real.mul_self_sqrt hδ]
    _ ≤ 1 * Real.sqrt δ := mul_le_mul_of_nonneg_right hmul (Real.sqrt_nonneg _)
    _ = _ := one_mul _

end WaveTurbulence.LGSpine
