/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.ConstantAbsorption

/-!
# The interpolation and cutoff losses fit the source tree exponent

The endpoint estimates have the same bulk exponent. The two-link loss
and one absorbed cutoff constant leave room inside the printed `100dηg`.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Pure scalar loss accounting for the common causal extension. -/
theorem tree_interpolation_scale_le {d n g : ℕ} (hd : 1 ≤ d) (hg : 1 ≤ g)
    {B C q η L : ℝ} (hB : 0 ≤ B) (hη : 0 ≤ η) (hL : 1 ≤ L)
    (hC : C ≤ L ^ (η * g)) :
    C * (B ^ n * L ^ (-(q - 2 * η) * g)) * L ^ (16 * (d : ℝ) * η) ≤
      B ^ n * L ^ (-(q - 100 * (d : ℝ) * η) * g) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hgR : 1 ≤ (g : ℝ) := by exact_mod_cast hg
  have hdη : η ≤ (d : ℝ) * η := by
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hdR hη)
  have hG : η * g ≤ (d : ℝ) * η * g :=
    mul_le_mul_of_nonneg_right hdη (Nat.cast_nonneg g)
  have hD : (d : ℝ) * η ≤ (d : ℝ) * η * g :=
    le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg d) hη) hgR
  have hexp : η * g + -(q - 2 * η) * g + 16 * (d : ℝ) * η ≤
      -(q - 100 * (d : ℝ) * η) * g := by
    have hnon := mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hη) (Nat.cast_nonneg g)
    nlinarith only [hG, hD, hnon]
  calc
    _ ≤ L ^ (η * g) * (B ^ n * L ^ (-(q - 2 * η) * g)) * L ^ (16 * (d : ℝ) * η) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (mul_nonneg (pow_nonneg hB n) (Real.rpow_nonneg hLp.le _)))
        (Real.rpow_nonneg hLp.le _)
    _ = B ^ n * L ^ (η * g + -(q - 2 * η) * g + 16 * (d : ℝ) * η) := by
      rw [Real.rpow_add hLp, Real.rpow_add hLp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hexp) (pow_nonneg hB n)

end WaveTurbulence.Incoh
